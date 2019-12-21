{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
module CircuitNotation (plugin) where

-- import Debug.Trace

import System.IO.Unsafe

import FastString (mkFastString)
import qualified Data.Data as Data
import Data.Maybe (fromMaybe)

import Data.Either (partitionEithers)

import Bag

-- import Data.Typeable
import Control.Monad.IO.Class (MonadIO (..))

import qualified Data.Generics as SYB

import qualified ErrUtils    as Err
-- import qualified Pretty
import qualified GhcPlugins  as GHC
import           HsExtension (GhcPs, NoExt (..))
import           HsSyn
import           SrcLoc
-- import           ErrUtils
import           HscTypes (throwOneError)
import qualified Outputable

import Control.Exception

import System.IO
import qualified OccName

import Control.Monad.State


-- | The name given to a 'port', i.e. the name of something either to the left of a '<-' or to the
-- right of a '-<'.
data PortName = PortName SrcSpan GHC.FastString

instance Show PortName where
  show (PortName _ fs) = GHC.unpackFS fs

fromRdrName :: GHC.RdrName -> GHC.FastString
fromRdrName = \case
  GHC.Unqual occName -> mkFastString (OccName.occNameString occName)
  GHC.Orig _ occName -> mkFastString (OccName.occNameString occName)
  nm -> mkFastString (deepShowD nm)

-- | A single circuit binding.
data Binding exp l = Binding
  { bCircuit :: exp
  , bOut     :: PortDescription l
  , bIn      :: PortDescription l
  } deriving (Functor)

-- | A description of a circuit with internal let bindings.
data CircuitQQ dec exp nm = CircuitQQ
  { circuitQQSlaves  :: PortDescription nm
  , circuitQQLets    :: [dec]
  , circuitQQBinds   :: [Binding exp nm]
  , circuitQQMasters :: PortDescription nm
  } deriving (Functor)

data CircuitState = CircuitState
  { cErrors   :: Bag Err.ErrMsg
  }

newtype CircuitM a = CircuitM (StateT CircuitState GHC.Hsc a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadState CircuitState)

liftHsc :: GHC.Hsc a -> CircuitM a
liftHsc = CircuitM . lift

instance GHC.HasDynFlags CircuitM where
  getDynFlags = liftHsc GHC.getDynFlags

runCircuitM :: CircuitM a -> GHC.Hsc a
runCircuitM (CircuitM m) = do
  let emptyCircuitState = CircuitState
        { cErrors = emptyBag
        }
  (a, s) <- runStateT m emptyCircuitState
  let errs = cErrors s
  when (not $ isEmptyBag errs) $ liftIO . throwIO $ GHC.mkSrcErr errs
  pure a

-- PortDescription -----------------------------------------------------

data PortDescription a
  = Tuple [PortDescription a]
  | Vec [PortDescription a]
  | Ref a
  | Lazy (PortDescription a)
  | PortErr SrcSpan Err.MsgDoc
  deriving (Foldable, Functor, Traversable)

tupP :: p ~ GhcPs => [LPat p] -> LPat p
tupP pats = noLoc $ TuplePat NoExt pats GHC.Boxed

vecP :: p ~ GhcPs => [LPat p] -> LPat p
vecP pats = noLoc $ ListPat NoExt pats

varP :: p ~ GhcPs => SrcSpan -> String -> LPat p
varP loc nm = L loc $ VarPat NoExt (L loc $ var nm)

-- Parsing -------------------------------------------------------------

err :: SrcSpan -> String -> CircuitM Err.ErrMsg
err loc msg = do
  dflags <- GHC.getDynFlags
  let errMsg = Err.mkLocMessageAnn Nothing Err.SevFatal loc (Outputable.text msg)
  pure $
    Err.mkErrMsg dflags loc Outputable.alwaysQualify errMsg

-- | "parse" a circuit, i.e. convert it from ghc's ast to our representation of a circuit.
parseCircuit
  :: p ~ GhcPs
  => LHsExpr p
  -> CircuitM (CircuitQQ (LHsBind p) (LHsExpr p) PortName)
parseCircuit = \case
  L _ (HsLam _ (MG _x alts _origin)) -> let
    [L _ (Match _matchX _matchContext [matchPats] matchGr)] = unL alts

    slaves :: PortDescription PortName
    slaves = bindSlave matchPats

    GRHSs _grX grHss _grLocalBinds = matchGr
    [L _ (GRHS _ _ (L loc body))] = grHss
    in case body of
      HsDo _x _stmtContext (L _ (unsnoc -> Just (stmts, finStmt))) -> do
        masters <-
          case finStmt of
            L _ (BodyStmt _bodyX bod _idr _idr') -> pure $ bindMaster bod
            L finLoc stmt ->
              throwOneError =<< err finLoc ("unhandled final stmt " <> show (Data.toConstr stmt))

        let (lets, bindings) = handleStmts stmts

        pure CircuitQQ
          { circuitQQSlaves = slaves
          , circuitQQLets = lets
          , circuitQQBinds = bindings
          , circuitQQMasters = masters
          }
      -- the simple case without do notation
      master ->
        let masters = bindMaster (L loc master)
        in pure CircuitQQ
          { circuitQQSlaves = slaves
          , circuitQQLets = []
          , circuitQQBinds = []
          , circuitQQMasters = masters
          }

  L _ (HsPar _ lexp) -> parseCircuit lexp

  L loc e -> do
    throwOneError =<< err loc ("Unable to handle circuit expression " <> show (Data.toConstr e))

handleStmts
  :: (p ~ GhcPs)
  => [ExprLStmt p] -> ([LHsBind p], [Binding (LHsExpr p) PortName])
handleStmts stmts = let
  (localBinds, bindings) = partitionEithers $ map (handleStmt . unL) stmts
  binds = flip concatMap localBinds \case
    L _ (HsValBinds _ (ValBinds _ valBinds _sigs)) -> bagToList valBinds
    _ -> error $ "Unhandled bind"

  in (binds, bindings)

handleStmt
  :: (p ~ GhcPs, loc ~ SrcSpan, idL ~ GhcPs)
  => StmtLR idL idR (LHsExpr p)
  -> Either (LHsLocalBindsLR idL idR) (Binding (LHsExpr p) PortName)
handleStmt = \case
  LetStmt _xlet letBind -> Left letBind
  BodyStmt _xbody body _idr _idr' -> Right (bodyBinding Nothing body)
  BindStmt _xbody bind body _idr _idr' -> Right (bodyBinding (Just $ bindSlave bind) body)
  _ -> error $ "Unhandled stmt"

-- | Turn patterns to the left of a @<-@ into a PortDescription.
bindSlave :: p ~ GhcPs => LPat p -> PortDescription PortName
bindSlave = \case
  L _ (VarPat _ (L loc rdrName)) -> Ref (PortName loc (fromRdrName rdrName))
  L _ (TuplePat _ lpat _) -> Tuple $ fmap bindSlave lpat
  L loc pat ->
    PortErr loc
            (Err.mkLocMessageAnn
              Nothing
              Err.SevFatal
              loc
              (Outputable.text $ "Unhandled pattern " <> show (Data.toConstr pat))
              )

-- | Turn expressions to the right of a @-<@ into a PortDescription.
bindMaster :: p ~ GhcPs => LHsExpr p -> PortDescription PortName
bindMaster = \case
  L _ (HsVar _xvar (L loc rdrName)) -> Ref (PortName loc (fromRdrName rdrName))
  L _ (ExplicitTuple _ tups _) -> let
    vals = fmap (\(L _ (Present _ expr)) -> expr) tups
    in Tuple $ fmap bindMaster vals
  L _ (ExplicitList _ _syntaxExpr exprs) -> Vec $ fmap bindMaster exprs
  L loc expr ->
    case expr of
      HsArrApp _xapp cir arg _ _ ->
        case cir of
          L _ (HsVar _ (L _ (GHC.Unqual occ)))
            | OccName.occNameString occ == "idC" -> bindMaster arg
            -- | otherwise -> let
            --     resName = mkRdrUnqual (var "uncaptureable:name")
            --     in (Ref resName, [bodyBinding (Just resName) arg])
          _ -> error "Can only handle final idC at the moment!"
      _ -> PortErr loc
        (Err.mkLocMessageAnn
          Nothing
          Err.SevFatal
          loc
          (Outputable.text $ "Unhandled expression " <> show (Data.toConstr expr))
          )

-- Checking ------------------------------------------------------------

checkCircuit :: p ~ GhcPs => CircuitQQ (LHsBind p) (LHsExpr p) PortName -> CircuitM ()
checkCircuit cQQ = do
  checkMatching cQQ

checkMatching :: p ~ GhcPs => CircuitQQ (LHsBind p) (LHsExpr p) PortName -> CircuitM ()
checkMatching CircuitQQ {..} = do
  -- data CircuitQQ dec exp nm = CircuitQQ
  --   { circuitQQSlaves  :: PortDescription nm
  --   , circuitQQLets    :: [dec]
  --   , circuitQQBinds   :: [Binding exp nm]
  --   , circuitQQMasters :: PortDescription nm
  --   } deriving (Functor)
  pure ()


-- Creating ------------------------------------------------------------

bindWithSuffix :: p ~ GhcPs => GHC.DynFlags -> String -> PortDescription PortName -> LPat p
bindWithSuffix dflags suffix = \case
  Tuple ps -> tupP $ fmap (bindWithSuffix dflags suffix) ps
  Vec ps   -> vecP $ fmap (bindWithSuffix dflags suffix) ps
  Ref (PortName loc fs) -> varP loc (GHC.unpackFS fs <> suffix)
  PortErr loc msgdoc -> unsafePerformIO . throwOneError $
    Err.mkLongErrMsg dflags loc Outputable.alwaysQualify (Outputable.text "Unhandled bind") msgdoc
  Lazy _ -> error "bindWithSuffix Lazy not handled" -- tildeP $ bindWithSuffix suffix p

bindOutputs
  :: p ~ GhcPs
  => GHC.DynFlags
  -> PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LPat p
bindOutputs dflags slaves masters = tupP [m2s, s2m]
  where
  -- super hacky: at this point we can generate names not possible in
  -- normal haskell (i.e. with spaces or colons). This is used to
  -- emulate non-captuable names.
  m2s = bindWithSuffix dflags ":M2S" masters
  s2m = bindWithSuffix dflags ":S2M" slaves

expWithSuffix :: p ~ GhcPs => String -> PortDescription PortName -> LHsExpr p
expWithSuffix suffix = \case
  Tuple ps -> tupE noSrcSpan $ fmap (expWithSuffix suffix) ps
  Vec ps   -> vecE noSrcSpan $ fmap (expWithSuffix suffix) ps
  Ref (PortName loc fs)   -> varE loc (var $ GHC.unpackFS fs <> suffix)
  -- lazyness only affects the pattern side
  Lazy p   -> expWithSuffix suffix p
  PortErr _ _ -> error "expWithSuffix PortErr!"

createInputs
  :: p ~ GhcPs
  => PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LHsExpr p
createInputs slaves masters = tupE noSrcSpan [m2s, s2m]
  where
  m2s = expWithSuffix ":M2S" masters
  s2m = expWithSuffix ":S2M" slaves

decFromBinding :: p ~ GhcPs => GHC.DynFlags -> Binding (LHsExpr p) PortName -> HsBind p
decFromBinding dflags Binding {..} = do
  let bindPat  = bindOutputs dflags bOut bIn
      inputExp = createInputs bIn bOut
      bod = runCircuitFun noSrcSpan `appE` bCircuit `appE` inputExp
   in patBind bindPat bod

patBind :: p ~ GhcPs => LPat p -> LHsExpr p -> HsBindLR p p
patBind lhs expr = PatBind NoExt lhs rhs ([], [])
  where
    rhs = GRHSs NoExt [gr] (noLoc $ EmptyLocalBinds NoExt)
    gr  = L (getLoc expr) (GRHS NoExt [] expr)

letE
  :: p ~ GhcPs
  => SrcSpan
  -- ^ location for top level let bindings
  -> [LHsBindLR p p]
  -- ^ let bindings
  -> LHsExpr p
  -- ^ final `in` expressions
  -> LHsExpr p
letE loc binds expr = L loc (HsLet NoExt localBinds expr)
  where
    localBinds :: LHsLocalBindsLR GhcPs GhcPs
    localBinds = L loc $ HsValBinds NoExt valBinds

    valBinds :: HsValBindsLR GhcPs GhcPs
    valBinds = ValBinds NoExt hsBinds sigs

    sigs :: [LSig GhcPs]
    sigs = []

    hsBinds :: LHsBindsLR GhcPs GhcPs
    hsBinds = listToBag binds

circuitConstructor :: p ~ GhcPs => SrcSpan -> LHsExpr p
circuitConstructor loc = varE loc (con "Circuit")

runCircuitFun :: p ~ GhcPs => SrcSpan -> LHsExpr p
runCircuitFun loc = varE loc (var "runCircuit")

appE :: p ~ GhcPs => LHsExpr p -> LHsExpr p -> LHsExpr p
appE fun arg = L noSrcSpan $ HsApp NoExt fun arg

varE :: p ~ GhcPs => SrcSpan -> GHC.RdrName -> LHsExpr p
varE loc rdr = L loc (HsVar NoExt (L loc rdr))

var :: String -> GHC.RdrName
var = GHC.Unqual . OccName.mkVarOcc

con :: String -> GHC.RdrName
con = GHC.Unqual . OccName.mkDataOcc

vecE :: p ~ GhcPs => SrcSpan -> [LHsExpr p] -> LHsExpr p
vecE loc elems = L loc $ ExplicitList NoExt Nothing elems

tupE :: p ~ GhcPs => SrcSpan -> [LHsExpr p] -> LHsExpr p
tupE loc elems = L loc $ ExplicitTuple NoExt tupArgs GHC.Boxed
  where
    tupArgs = map (\arg@(L l _) -> L l (Present NoExt arg)) elems

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin
  { GHC.parsedResultAction = \_cliOptions -> pluginImpl
  }

pluginImpl :: GHC.ModSummary -> GHC.HsParsedModule -> GHC.Hsc GHC.HsParsedModule
pluginImpl _modSummary m = do
    dflags <- GHC.getDynFlags
    debug $ GHC.showPpr dflags (GHC.hpm_module m )
    hpm_module' <- transform (GHC.hpm_module m)
    let module' = m { GHC.hpm_module = hpm_module' }
    return module'

debug :: MonadIO m => String -> m ()
debug = liftIO . hPutStrLn stderr
-- debug _ = pure ()

unL :: Located a -> a
unL (L _ a) = a

deepShowD :: Data.Data a => a -> String
deepShowD a = show (Data.toConstr a) <>
  " (" <> (unwords . fst) (SYB.gmapM (\x -> ([show $ Data.toConstr x], x)) a) <> ")"
  -- " (" <> (unwords . fst) (SYB.gmapM (\x -> ([deepShowD x], x)) a) <> ")"


bodyBinding
  :: (p ~ GhcPs, loc ~ SrcSpan)
  => Maybe (PortDescription PortName)
  -> GenLocated loc (HsExpr p)
  -> Binding (LHsExpr p) PortName
bodyBinding mInput lexpr@(L _loc expr) =
  case expr of
    HsArrApp _xhsArrApp circuit port HsFirstOrderApp True ->
      Binding
        { bCircuit = circuit
        , bOut     = bindMaster port
        , bIn      = fromMaybe (Tuple []) mInput
        }

    _ ->
      Binding
        { bCircuit = lexpr
        , bOut     = Tuple []
        , bIn      = fromMaybe (error "standalone expressions not allowed") mInput
        }

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = Nothing
unsnoc [x] = Just ([], x)
unsnoc (x:xs) = Just (x:a, b)
    where Just (a,b) = unsnoc xs

mkCircuit
  :: p ~ GhcPs
  => PortDescription PortName
  -- ^ slave ports
  -> [LHsBindLR p p]
  -- ^ let bindings
  -> PortDescription PortName
  -- ^ master ports
  -> CircuitM (LHsExpr p)
  -- ^ circuit
mkCircuit slaves lets masters = do
  dflags <- GHC.getDynFlags
  let pats = bindOutputs dflags masters slaves
      res  = createInputs slaves masters

      body :: LHsExpr GhcPs
      body = letE noSrcSpan lets res

  pure $ circuitConstructor noSrcSpan `appE` lamE [pats] body

circuitQQExpM
  :: p ~ GhcPs
  => CircuitQQ (LHsBind p) (LHsExpr p) PortName
  -> CircuitM (LHsExpr p)
circuitQQExpM c@CircuitQQ {..} = do
  checkCircuit c
  dynflags <- GHC.getDynFlags
  let decs = concat
        [ circuitQQLets
        , fmap (noLoc . decFromBinding dynflags) circuitQQBinds
        ]
  mkCircuit circuitQQSlaves decs circuitQQMasters

lamE :: p ~ GhcPs => [LPat p] -> LHsExpr p -> LHsExpr p
lamE pats expr = noLoc $ HsLam NoExt mg
  where
    mg = MG NoExt matches GHC.Generated

    matches :: Located [LMatch GhcPs (LHsExpr GhcPs)]
    matches = noLoc $ [singleMatch]

    singleMatch :: LMatch GhcPs (LHsExpr GhcPs)
    singleMatch = noLoc $ Match NoExt LambdaExpr pats grHss

    grHss :: GRHSs GhcPs (LHsExpr GhcPs)
    grHss = GRHSs NoExt [grHs] (noLoc $ EmptyLocalBinds NoExt)

    grHs :: LGRHS GhcPs (LHsExpr GhcPs)
    grHs = noLoc $ GRHS NoExt [] expr

-- finalStmt
--   :: p ~ GhcPs
--   => LHsExpr p
--   -> (PortDescription PortName, [Binding (LHsExpr GhcPs) PortName])
-- finalStmt = \case
--   L loc (HsArrApp _ cir arg _ _) ->
--     case cir of
--           L _ (HsVar _ (L _ (GHC.Unqual occ)))
--             | OccName.occNameString occ == "idC" -> (bindMaster arg, [])
--             -- | otherwise  -> let
--             --     resName = PortName loc (mkFastString "uncaptureable:name")
--             --     binding :: Binding (LHsExpr GhcPs) PortName
--             --     binding = bodyBinding (Just _) (varE loc (var "uncaptureable:name"))
--             --      in (Ref resName, [binding])
--             --     -- in (Ref resName, [bodyBinding (Just arg) resName])
-- 
--       -- HsArrApp _xapp _idC (L _ var) _ _ ->
--       --   case var of
--       --     HsVar _ (L l rdr) ->
--       --       case rdr of
--       --         GHC.Unqual occ ->
--       --           Ref (PortName l (mkFastString $ OccName.occNameString occ))
-- 
--       -- Ref (PortName loc (mkFastString "bindMaster: Can't handle this pattern yet"))
--   -- _ -> error "can't handle this pattern yet"
-- 
--             -- case out of
--             --   Exts.Qualifier l e@(Exts.InfixApp _ var ArrIn source) ->
--             --     case var of
--             --       -- with idC there's no need for extra bindings
--             --       Exts.Var _ (Exts.UnQual _ (Exts.Ident _ "idC")) -> (portExp source, [])
--             --       _ -> let -- TODO: this should be a non-captureable name
--             --                resName = Exts.Ident l "cQQResult"
--             --            in  (Ref resName, [mkBinding (Exts.PVar undefined resName) e])

isCircuitVar :: p ~ GhcPs => HsExpr p -> Bool
isCircuitVar = \case
  HsVar _ (L _ v) -> v == GHC.mkVarUnqual "circuit"
  _               -> False

isDollar :: p ~ GhcPs => HsExpr p -> Bool
isDollar = \case
  HsVar _ (L _ v) -> v == GHC.mkVarUnqual "$"
  _               -> False

transform
    :: GHC.Located (HsModule GhcPs)
    -> GHC.Hsc (GHC.Located (HsModule GhcPs))
transform = SYB.everywhereM (SYB.mkM transform') where
  transform' :: LHsExpr GhcPs -> GHC.Hsc (LHsExpr GhcPs)
  transform' (L _ (HsApp _xapp (L _ circuitVar) lappB))
    | isCircuitVar circuitVar = do
      debug "HsApp!"
      runCircuitM $ transformCircuit lappB

  transform' (L _ (OpApp _xapp (L _ circuitVar) (L _ infixVar) appR))
    | isCircuitVar circuitVar && isDollar infixVar = do
      runCircuitM $ transformCircuit appR

  transform' e = pure e

transformCircuit :: p ~ GhcPs => LHsExpr p -> CircuitM (LHsExpr p)
transformCircuit e = do
  dflags <- GHC.getDynFlags
  let pp :: GHC.Outputable a => a -> String
      pp = GHC.showPpr dflags
  cqq <- parseCircuit e
  expr <- circuitQQExpM cqq
  debug $ pp expr
  pure expr

-- showC :: Data.Data a => a -> String
-- showC a = show (typeOf a) <> " " <> show (Data.toConstr a)

--
--


-- mySuperSimpleLet :: p ~ GhcPs => LHsExpr p
-- mySuperSimpleLet = letE noSrcSpan binds end
--   where
--     binds :: [LHsBindLR GhcPs GhcPs]
--     binds = [noLoc $ patBind lhs rhs]
--     lhs = varP noSrcSpan "lhs"
--     rhs = varE noSrcSpan (var "rhs")
--     end = varE noSrcSpan (var "myVar")



--
--
--
--  -------------------------------------------------------------------------------
--  -- Expression
--  -------------------------------------------------------------------------------
--
--  transformExpr
--      :: MonadIO m
--      => GHC.DynFlags
--      -> LHsExpr GhcPs
--      -> m (LHsExpr GhcPs)
--  transformExpr dflags expr@(L _e OpApp {}) = do
--      let bt = matchOp expr
--      let result = idiomBT bt
--      debug $ "RES : " ++ GHC.showPpr dflags result
--      return result
--  transformExpr dflags expr = do
--      let (f :| args) = matchApp expr
--      let f' = pureExpr f
--      debug $ "FUN : " ++ GHC.showPpr dflags f
--      debug $ "FUN+: " ++ GHC.showPpr dflags f'
--      for_ (zip args args) $ \arg ->
--          debug $ "ARG : " ++ GHC.showPpr dflags arg
--      let result = foldl' apply f' args
--      debug $ "RES : " ++ GHC.showPpr dflags result
--      return result
--
--  -------------------------------------------------------------------------------
--  -- Pure
--  -------------------------------------------------------------------------------
--
--  -- f ~> pure f
--  pureExpr :: LHsExpr GhcPs -> LHsExpr GhcPs
--  pureExpr (L l f) =
--      L l $ HsApp NoExt (L l' (HsVar NoExt (L l' pureRdrName))) (L l' f)
--    where
--      l' = GHC.noSrcSpan
--
--  pureRdrName :: GHC.RdrName
--  pureRdrName = GHC.mkRdrUnqual (GHC.mkVarOcc "pure")
--
--  -- x y ~> x <|> y
--  altExpr :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
--  altExpr x y =
--      L l' $ OpApp NoExt x (L l' (HsVar NoExt (L l' altRdrName))) y
--    where
--      l' = GHC.noSrcSpan
--
--  altRdrName :: GHC.RdrName
--  altRdrName = GHC.mkRdrUnqual (GHC.mkVarOcc "<|>")
--
--  -- f x ~> f <$> x
--  fmapExpr :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
--  fmapExpr f x =
--      L l' $ OpApp NoExt f (L l' (HsVar NoExt (L l' fmapRdrName))) x
--    where
--      l' = GHC.noSrcSpan
--
--  fmapRdrName :: GHC.RdrName
--  fmapRdrName = GHC.mkRdrUnqual (GHC.mkVarOcc "<$>")
--
--  -- f x ~> f <*> x
--  apExpr :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
--  apExpr f x =
--      L l' $ OpApp NoExt f (L l' (HsVar NoExt (L l' apRdrName))) x
--    where
--      l' = GHC.noSrcSpan
--
--  apRdrName :: GHC.RdrName
--  apRdrName = GHC.mkRdrUnqual (GHC.mkVarOcc "<*>")
--
--  -- f x -> f <* x
--  birdExpr :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
--  birdExpr f x =
--      L l' $ OpApp NoExt f (L l' (HsVar NoExt (L l' birdRdrName))) x
--    where
--      l' = GHC.noSrcSpan
--
--  birdRdrName :: GHC.RdrName
--  birdRdrName = GHC.mkRdrUnqual (GHC.mkVarOcc "<*")
--
--  -- f x -y z  ->  (((pure f <*> x) <* y) <*> z)
--  apply :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
--  apply f (L _ (HsPar _ (L _ (HsApp _ (L _ (HsVar _ (L _ voidName'))) x))))
--      | voidName' == voidName = birdExpr f x
--  apply f x                   = apExpr f x
--
--  voidName :: GHC.RdrName
--  voidName = GHC.mkRdrUnqual (GHC.mkVarOcc "void")
--
--  -------------------------------------------------------------------------------
--  -- Function application maching
--  -------------------------------------------------------------------------------
--
--  -- | Match nested function applications, 'HsApp':
--  -- f x y z ~> f :| [x,y,z]
--  --
--  matchApp :: LHsExpr p -> NonEmpty (LHsExpr p)
--  matchApp (L _ (HsApp _ f x)) = neSnoc (matchApp f) x
--  matchApp e = pure e
--
--  neSnoc :: NonEmpty a -> a -> NonEmpty a
--  neSnoc (x :| xs) y = x :| xs ++ [y]
--
--  -------------------------------------------------------------------------------
--  -- Operator application matching
--  -------------------------------------------------------------------------------
--
--  -- | Match nested operator applications, 'OpApp'.
--  -- x + y * z ~>  Branch (+) (Leaf x) (Branch (*) (Leaf y) (Leaf z))
--  matchOp :: LHsExpr p -> BT (LHsExpr p)
--  matchOp (L _ (OpApp _  lhs op rhs)) = Branch (matchOp lhs) op (matchOp rhs)
--  matchOp x = Leaf x
--
--  -- | Non-empty binary tree, with elements at branches too.
--  data BT a = Leaf a | Branch (BT a) a (BT a)
--
--  -- flatten: note that leaf is returned as is.
--  idiomBT :: BT (LHsExpr GhcPs) -> LHsExpr GhcPs
--  idiomBT (Leaf x)            = x
--  idiomBT (Branch lhs op rhs) = fmapExpr op (idiomBT lhs) `apExpr` idiomBT rhs
--
--  -------------------------------------------------------------------------------
--  -- List Comprehension
--  -------------------------------------------------------------------------------
--
--  matchListComp :: [LStmt GhcPs (LHsExpr GhcPs)] -> Maybe [LHsExpr GhcPs]
--  matchListComp [L _ (BodyStmt _ expr2 _ _), L _ (LastStmt _ expr1 _ _)] =
--      Just [expr1, expr2]
--  matchListComp [L _ (ParStmt _ blocks _ _), L _ (LastStmt _ expr1 _ _)] = do
--      exprs <- for blocks $ \bl -> case bl of
--          ParStmtBlock _ [L _ (BodyStmt _ e _ _)] _ _ -> Just e
--          _ -> Nothing
--      return $ expr1 : exprs
--  matchListComp _ = Nothing
--
--  -------------------------------------------------------------------------------
--  -- Location checker
--  -------------------------------------------------------------------------------
--
--  -- Check that spans are right inside each others, i.e. we match
--  -- that there are no spaces between parens and brackets
--  inside :: SrcSpan -> SrcSpan -> Bool
--  inside (RealSrcSpan a) (RealSrcSpan b) = and
--      [ srcSpanStartLine a == srcSpanStartLine b
--      , srcSpanEndLine a == srcSpanEndLine b
--      , srcSpanStartCol a + 1 == srcSpanStartCol b
--      , srcSpanEndCol a == srcSpanEndCol b + 1
--      ]
--  inside _ _ = False
--    -- noLoc $ HsValBinds NoExt binds
--    -- where
--    --   binds :: HsValBindsLR GhcPs GhcPs
--    --   binds = ValBinds NoExt hsBinds sigs
--    --   sigs = []
--    --   hsBinds :: LHsBindsLR GhcPs GhcPs
--    --   hsBinds = listToBag . (:[]) $ myCoolBind
--
--    --   myCoolBind :: LHsBindLR GhcPs GhcPs
--    --   -- myCoolBind = noLoc $ VarBind NoExt myBindId myExpr False
--    --   myCoolBind = noLoc $ PatBind NoExt lhs rhs ([],[])
--
--    --   lhs :: LPat GhcPs
--    --   lhs = noLoc $ TuplePat NoExt pats GHC.Boxed
--
--    --   pats :: [LPat GhcPs]
--    --   pats =
--    --     [ noLoc $ VarPat NoExt (noLoc $ mkName "yo")
--    --     , noLoc $ VarPat NoExt (noLoc $ mkName "la")
--    --     ]
--
--    --   mkName :: String -> GHC.RdrName
--    --   mkName = GHC.Unqual . OccName.mkVarOcc
--
--    --   rhs :: GRHSs GhcPs (LHsExpr GhcPs)
--    --   rhs = GRHSs NoExt [myGr] (noLoc $ EmptyLocalBinds NoExt)
--
--    --   myGr :: LGRHS GhcPs (LHsExpr GhcPs)
--    --   myGr = noLoc $ GRHS NoExt [] myVar
--
--    --   myVar :: LHsExpr GhcPs
--    --   myVar = noLoc $ HsVar NoExt (noLoc $ mkName "ah")
--
--
--  -- patBind :: p ~ GhcPs => LPat p -> LHsExpr p -> HsBindLR p p
--
--  -- binding :: p ~ GhcPs => Binding (LHsExpr p) PortName -> HsBind p
--  -- binding Binding {..} = patBind pat expr
--  --   where
--  --     pat =
--
--  -- mySuperSimpleLet :: p ~ GhcPs => HsExpr p
--  -- mySuperSimpleLet = HsLet NoExt mySuperSimpleLocalBind myIn
--  --   where
--  --     myIn = noLoc $ HsVar NoExt (noLoc myVarId)
--  --     myVarId = GHC.Unqual (OccName.mkVarOcc "yo")
--
--
--    -- let bindPat  = bindOutputs bOut bIn
--    --     inputExp = createInputs bIn bOut
--    --     bod = varE 'runCircuit' `appE` pure bCircuit `appE` inputExp
--    -- valD bindPat (normalB bod) []
--
--
--
--  -- decFromBinding :: Binding String -> Q Dec
--  -- decFromBinding Binding {..} = do
--  --   let bindPat  = bindOutputs bOut bIn
--  --       inputExp = createInputs bIn bOut
--  --       bod = varE 'runCircuit' `appE` pure bCircuit `appE` inputExp
--  --   valD bindPat (normalB bod) []
--
--  -- plugin :: GHC.Plugin
--  -- plugin = GHC.defaultPlugin
--  --   { GHC.renamedResultAction = \_cliOptions _ _ -> error "made it here"
--  --   }
--
--  -- class GHC.Outputable a where
--  --     GHC.ppr :: a -> GHC.SDoc
--  --       GHC.pprPrec :: Rational -> a -> GHC.SDoc
--
--
--      -- transform' e@(L l (HsPar _ (L l' (ExplicitList  _ Nothing exprs)))) | inside l l' =
--      --     case exprs of
--      --         [expr] -> do
--      --             expr' <- transformExpr dflags expr
--      --             return (L l (HsPar NoExt expr'))
--      --         _ -> do
--      --             liftIO $ GHC.putLogMsg dflags GHC.NoReason Err.SevWarning l (GHC.defaultErrStyle dflags) $
--      --                 GHC.text "Non singleton idiom bracket list"
--      --                 GHC.$$
--      --                 GHC.ppr exprs
--      --             return e
--      -- transform' (L l (HsPar _ (L l' (HsDo _ ListComp (L _ stmts)))))
--      --     | inside l l', Just exprs <- matchListComp stmts = do
--      --         for_ exprs $ \expr ->
--      --             debug $ "ALT: " ++ GHC.showPpr dflags expr
--  -- --            for_ (zip stmts [0..]) $ \(stmt, i) -> do
--  -- --                debug $ show i ++ " ==> " ++ SYB.gshow stmt
--      --         exprs' <- traverse (transformExpr dflags) exprs
--      --         return (foldr1 altExpr exprs')
--      -- transform' expr =
--      --     return expr
--
--      -- transform' e@(L l (HsLet _xhsLet localBinds inExpr)) = do
--      --   case localBinds of
--      --     L _ (HsValBinds NoExt binds) ->
--      --       case binds of
--      --         ValBinds NoExt hsBinds sigs ->
--      --           case bagToList hsBinds of
--      --             -- [L _ (FunBind NoExt bindId expr _)] ->
--      --             [L _ (VarBind NoExt bindId expr _)] ->
--      --               debug $ deepShowD bindId
--      --             [L _ (PatBind NoExt (L _ lhs) rhs ticks)] -> do
--      --               debug $ "lhs: " <> deepShowD lhs
--      --               case lhs of
--      --                 TuplePat _xTuple pats GHC.Boxed ->
--      --                   case pats of
--      --                     [ L _ (VarPat _ (L _ (GHC.Unqual nm1)))
--      --                       , L _ (VarPat _ (L _ (GHC.Unqual nm2)))
--      --                       ]
--      --                       -> do debug $ "p1: " <> OccName.occNameString nm1
--      --                             debug $ "p2: " <> OccName.occNameString nm2
--      --                     _ -> for_ pats $ debug . deepShowD
--      --               debug $ "rhs: " <> deepShowD rhs
--      --               case rhs of
--      --                 GRHSs _ body (L _ localBinds) -> do
--      --                   for_ body $ \(L _ (GRHS _ guard (L _ bod))) -> do
--      --                     debug $ "grhs_body: " <> deepShowD bod
--      --                   debug $ "localBinds: " <> deepShowD localBinds
--                  -- [L _ vb] -> debug $ deepShowD vb
--        -- debug $ deepShowD localBinds
--        -- pure e
--
--  -- mkNewExprRn :: TcM (LHsExpr GhcTc)
--  -- mkNewExprRn = do
--  --   -- The names we want to use happen to already be in PrelNames so we use
--  --   -- them directly.
--  --   let print_occ = mkRdrUnqual (mkVarOcc "print")
--  --   print_name <- lookupOccRn print_occ
--  --   let raw_expr = nlHsApp (nlHsVar print_name) (nlHsVar (dataConName unitDataCon))
--  --   io_tycon <- tcLookupTyCon ioTyConName
--  --   let exp_type = mkTyConApp io_tycon [unitTy]
--  --   typecheckExpr exp_type raw_expr
--
--  -- mkNewExprPs :: TcM (LHsExpr GhcTc)
--  -- mkNewExprPs  = do
--
--  --   let
--  --     print_occ = mkRdrUnqual (mkVarOcc "print")
--  --     unit_occ = nameRdrName (dataConName unitDataCon)
--  --     ps_expr = nlHsApp (nlHsVar print_occ)
--  --                       (nlHsVar unit_occ)
--
--  --   io_tycon <- tcLookupTyCon ioTyConName
--  --   let exp_type = mkTyConApp io_tycon [unitTy]
--  --   renameExpr ps_expr >>= typecheckExpr exp_type
--
