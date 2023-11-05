{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

Notation for describing the 'Circuit' type.
-}

{-# LANGUAGE BlockArguments             #-}
{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE PackageImports             #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- TODO: Fix warnings introduced by GHC 9.2
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CircuitNotation
  ( plugin
  , mkPlugin
  , thName
  , ExternalNames (..)
  ) where

-- base
import           Control.Exception
import qualified Data.Data              as Data
import           Data.Default
import           Data.Maybe             (fromMaybe)
#if __GLASGOW_HASKELL__ >= 900
#else
import           SrcLoc hiding (noLoc)
#endif
import           System.IO.Unsafe
import           Data.Typeable

-- ghc
import qualified Language.Haskell.TH    as TH
import qualified GHC

#if __GLASGOW_HASKELL__ >= 902
import           GHC.Types.SourceError  (throwOneError)
import qualified GHC.Driver.Env         as GHC
import qualified GHC.Types.SourceText   as GHC
import qualified GHC.Types.SourceError  as GHC
import qualified GHC.Driver.Ppr         as GHC
#elif __GLASGOW_HASKELL__ >= 900
import           GHC.Driver.Types       (throwOneError)
import qualified GHC.Driver.Types       as GHC
#else
import           HscTypes               (throwOneError)
#endif

#if __GLASGOW_HASKELL__ == 900
import qualified GHC.Parser.Annotation     as GHC
#endif

#if __GLASGOW_HASKELL__ >= 900
import           GHC.Data.Bag
import           GHC.Data.FastString       (mkFastString, unpackFS)
import           GHC.Plugins               (PromotionFlag(NotPromoted))
import           GHC.Types.SrcLoc          hiding (noLoc)
import qualified GHC.Data.FastString       as GHC
import qualified GHC.Driver.Plugins        as GHC
import qualified GHC.Driver.Session        as GHC
import qualified GHC.Types.Basic           as GHC
import qualified GHC.Types.Name.Occurrence as OccName
import qualified GHC.Types.Name.Reader     as GHC
import qualified GHC.Utils.Error           as Err
import qualified GHC.Utils.Outputable      as GHC
import qualified GHC.Utils.Outputable      as Outputable
#else
import           Bag
import qualified ErrUtils               as Err
import           FastString             (mkFastString, unpackFS)
import qualified GhcPlugins             as GHC
import qualified OccName
import qualified Outputable
#endif

#if __GLASGOW_HASKELL__ > 808
import qualified GHC.ThToHs             as Convert
import           GHC.Hs
#if __GLASGOW_HASKELL__ >= 902
  hiding (locA)
#endif
#else
import qualified Convert
import           HsSyn                  hiding (noExt)
import           HsExtension            (GhcPs, NoExt (..))
#endif

#if __GLASGOW_HASKELL__ <= 806
import           PrelNames              (eqTyCon_RDR)
#elif __GLASGOW_HASKELL__ <= 810
import           TysWiredIn             (eqTyCon_RDR)
import           BasicTypes             (PromotionFlag( NotPromoted ))
#else
import           GHC.Builtin.Types      (eqTyCon_RDR)
#endif

#if __GLASGOW_HASKELL__ >= 902
import "ghc" GHC.Types.Unique.Map
#else
import GHC.Types.Unique.Map
#endif

import GHC.Types.Unique.Map.Extra

-- clash-prelude
import Clash.Prelude (Signal, Vec((:>), Nil))

-- lens
import qualified Control.Lens           as L
import           Control.Lens.Operators

-- mtl
import           Control.Monad.State

-- pretty-show
-- import qualified Text.Show.Pretty       as SP

-- syb
import qualified Data.Generics          as SYB

-- The stages of this plugin
--
-- 1. Go through the parsed module source and find usages of the circuit keyword (`transform`).
-- 2. Parse the circuit, either do notation or a one liner, go through each statement and convert it
--    to a CircuitQQ.
-- 3. Go through the CircuitQQ and check that everything is consistent (every master has a matching
--    slave).
-- 4. Convert the Bindings to let statements, at the same time build up a description of the types
--    to make the type descriptor helper.


-- Utils ---------------------------------------------------------------
isSomeVar :: (p ~ GhcPs) => GHC.FastString -> HsExpr p -> Bool
isSomeVar s = \case
  HsVar _ (L _ v) -> v == GHC.mkVarUnqual s
  _               -> False

isCircuitVar :: p ~ GhcPs => HsExpr p -> Bool
isCircuitVar = isSomeVar "circuit"

isDollar :: p ~ GhcPs => HsExpr p -> Bool
isDollar = isSomeVar "$"

-- | Is (-<)?
isFletching :: p ~ GhcPs => HsExpr p -> Bool
isFletching = isSomeVar "-<"

imap :: (Int -> a -> b) -> [a] -> [b]
imap f = zipWith f [0 ..]

-- Utils for backwards compat ------------------------------------------
#if __GLASGOW_HASKELL__ >= 902
type MsgDoc = Outputable.SDoc
type ErrMsg = Err.MsgEnvelope Err.DecoratedSDoc

locA :: SrcSpanAnn' a -> SrcSpan
locA = GHC.locA

noAnnSortKey :: AnnSortKey
noAnnSortKey = NoAnnSortKey
#else
type MsgDoc = Err.MsgDoc
type ErrMsg = Err.ErrMsg
type SrcSpanAnnA = SrcSpan
type SrcSpanAnnL = SrcSpan

noSrcSpanA :: SrcSpan
noSrcSpanA = noSrcSpan

noAnnSortKey :: NoExtField
noAnnSortKey = noExtField

emptyComments :: NoExtField
emptyComments = noExtField

locA :: a -> a
locA = id
#endif

#if __GLASGOW_HASKELL__ > 900
noExt :: EpAnn ann
noExt = EpAnnNotUsed
#elif __GLASGOW_HASKELL__ > 808
noExt :: NoExtField
noExt = noExtField
#else
noExt :: NoExt
noExt = NoExt

noExtField :: NoExt
noExtField = NoExt

type NoExtField = NoExt
#endif

mkErrMsg :: GHC.DynFlags -> SrcSpan -> Outputable.PrintUnqualified -> Outputable.SDoc -> ErrMsg
#if __GLASGOW_HASKELL__ >= 902
mkErrMsg _ = Err.mkMsgEnvelope
#else
mkErrMsg = Err.mkErrMsg
#endif

mkLongErrMsg :: GHC.DynFlags -> SrcSpan -> Outputable.PrintUnqualified -> Outputable.SDoc -> Outputable.SDoc -> ErrMsg
#if __GLASGOW_HASKELL__ >= 902
mkLongErrMsg _ = Err.mkLongMsgEnvelope
#else
mkLongErrMsg = Err.mkLongErrMsg
#endif

-- Types ---------------------------------------------------------------

-- | The name given to a 'port', i.e. the name of a variable either to the left of a '<-' or to the
--   right of a '-<'.
data PortName = PortName SrcSpanAnnA GHC.FastString
  deriving (Eq)

instance Show PortName where
  show (PortName _ fs) = GHC.unpackFS fs

data PortDescription a
    = Tuple [PortDescription a]
    | Vec SrcSpanAnnA [PortDescription a]
    | Ref a
    | Lazy SrcSpanAnnA (PortDescription a)
    | SignalExpr (LHsExpr GhcPs)
    | SignalPat (LPat GhcPs)
    | PortType (LHsType GhcPs) (PortDescription a)
    | PortErr SrcSpanAnnA MsgDoc
    deriving (Foldable, Functor, Traversable)

_Ref :: L.Prism' (PortDescription a) a
_Ref = L.prism' Ref (\case Ref a -> Just a; _ -> Nothing)

instance L.Plated (PortDescription a) where
  plate f = \case
    Tuple ps -> Tuple <$> traverse f ps
    Vec s ps -> Vec s <$> traverse f ps
    Lazy s p -> Lazy s <$> f p
    PortType t p -> PortType t <$> f p
    p -> pure p

-- | A single circuit binding. These are generated from parsing statements.
-- @
-- bOut <- bCircuit -< bIn
-- @
data Binding exp l = Binding
    { bCircuit :: exp
    , bOut     :: PortDescription l
    , bIn      :: PortDescription l
    }
    deriving (Functor)

data CircuitState dec exp nm = CircuitState
    { _cErrors        :: Bag ErrMsg
    , _counter        :: Int
    -- ^ unique counter for generated variables
    , _circuitSlaves  :: PortDescription nm
    -- ^ the final statement in a circuit
    , _circuitTypes   :: [LSig GhcPs]
    -- ^ type signatures in let bindings
    , _circuitLets    :: [dec]
    -- ^ user defined let expression inside the circuit
    , _circuitBinds   :: [Binding exp nm]
    -- ^ @out <- circuit <- in@ statements
    , _circuitMasters :: PortDescription nm
    -- ^ ports bound at the first lambda of a circuit
    , _portVarTypes :: UniqMap GHC.FastString (SrcSpanAnnA, LHsType GhcPs)
    -- ^ types of single variable ports
    , _portTypes :: [(LHsType GhcPs, PortDescription nm)]
    -- ^ type of more 'complicated' things (very far from vigorous)
    , _uniqueCounter :: Int
    -- ^ counter to keep internal variables "unique"
    , _circuitLoc :: SrcSpanAnnA
    -- ^ span of the circuit expression
    }

L.makeLenses 'CircuitState

-- | The monad used when running a single circuit.
newtype CircuitM a = CircuitM (StateT (CircuitState (LHsBind GhcPs) (LHsExpr GhcPs) PortName) GHC.Hsc a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadState (CircuitState (GenLocated SrcSpanAnnA (HsBindLR GhcPs GhcPs)) (GenLocated SrcSpanAnnA (HsExpr GhcPs)) PortName))

-- , MonadState (CircuitState (LHsBind GhcPs) (LHsExpr GhcPs) PortName)

instance GHC.HasDynFlags CircuitM where
  getDynFlags = (CircuitM . lift) GHC.getDynFlags

runCircuitM :: CircuitM a -> GHC.Hsc a
runCircuitM (CircuitM m) = do
  let emptyCircuitState = CircuitState
        { _cErrors = emptyBag
        , _counter = 0
        , _circuitSlaves = Tuple []
        , _circuitTypes = []
        , _circuitLets = []
        , _circuitBinds = []
        , _circuitMasters = Tuple []
        , _portVarTypes = emptyUniqMap
        , _portTypes = []
        , _uniqueCounter = 1
        , _circuitLoc = noSrcSpanA
        }
  (a, s) <- runStateT m emptyCircuitState
  let errs = _cErrors s
  unless (isEmptyBag errs) $ liftIO . throwIO $ GHC.mkSrcErr errs
  pure a


errM :: SrcSpan -> String -> CircuitM ()
errM loc msg = do
  dflags <- GHC.getDynFlags
  let errMsg = Err.mkLocMessageAnn Nothing Err.SevFatal loc (Outputable.text msg)
  cErrors %= consBag (mkErrMsg dflags loc Outputable.alwaysQualify errMsg)

-- ghc helpers ---------------------------------------------------------

-- It's very possible that most of these are already in the ghc library in some form. It's not the
-- easiest library to discover these kind of functions.

#if __GLASGOW_HASKELL__ >= 902
conPatIn :: GenLocated SrcSpanAnnN GHC.RdrName -> HsConPatDetails GhcPs -> Pat GhcPs
#else
conPatIn :: Located GHC.RdrName -> HsConPatDetails GhcPs -> Pat GhcPs
#endif
#if __GLASGOW_HASKELL__ >= 900
conPatIn loc con = ConPat noExt loc con
#else
conPatIn loc con = ConPatIn loc con
#endif

#if __GLASGOW_HASKELL__ >= 902
noEpAnn :: GenLocated SrcSpan e -> GenLocated (SrcAnn ann) e
noEpAnn (L l e) = L (SrcSpanAnn EpAnnNotUsed l) e

noLoc :: e -> GenLocated (SrcAnn ann) e
noLoc = noEpAnn . GHC.noLoc
#else
noLoc :: e -> Located e
noLoc = GHC.noLoc
#endif

tupP :: p ~ GhcPs => [LPat p] -> LPat p
tupP [pat] = pat
tupP pats = noLoc $ TuplePat noExt pats GHC.Boxed

vecP :: SrcSpanAnnA -> [LPat GhcPs] -> LPat GhcPs
vecP srcLoc = \case
  [] -> go []
  as -> L srcLoc $ ParPat noExt $ go as
  where
  go :: [LPat GhcPs] -> LPat GhcPs
  go (p@(L l0 _):pats) =
    let
#if __GLASGOW_HASKELL__ >= 902
      l1 = l0 `seq` noSrcSpanA
#else
      l1 = l0
#endif
    in
      L srcLoc $ conPatIn (L l1 (thName '(:>))) (InfixCon p (go pats))
  go [] = L srcLoc $ WildPat noExtField

varP :: SrcSpanAnnA -> String -> LPat GhcPs
varP loc nm = L loc $ VarPat noExtField (noLoc $ var nm)

tildeP :: SrcSpanAnnA -> LPat GhcPs -> LPat GhcPs
tildeP loc lpat = L loc (LazyPat noExt lpat)

hsBoxedTuple :: GHC.HsTupleSort
#if __GLASGOW_HASKELL__ >= 902
hsBoxedTuple = HsBoxedOrConstraintTuple
#else
hsBoxedTuple = HsBoxedTuple
#endif

tupT :: [LHsType GhcPs] -> LHsType GhcPs
tupT [ty] = ty
tupT tys = noLoc $ HsTupleTy noExt hsBoxedTuple tys

vecT :: SrcSpanAnnA -> [LHsType GhcPs] -> LHsType GhcPs
vecT s [] = L s $ HsParTy noExt (conT s (thName ''Vec) `appTy` tyNum s 0 `appTy` (varT s (genLocName s "vec")))
vecT s tys = L s $ HsParTy noExt (conT s (thName ''Vec) `appTy` tyNum s (length tys) `appTy` head tys)

tyNum :: SrcSpanAnnA -> Int -> LHsType GhcPs
tyNum s i = L s (HsTyLit noExtField (HsNumTy GHC.NoSourceText (fromIntegral i)))

appTy :: LHsType GhcPs -> LHsType GhcPs -> LHsType GhcPs
appTy a b = noLoc (HsAppTy noExtField a (parenthesizeHsType GHC.appPrec b))

appE :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
appE fun arg = L noSrcSpanA $ HsApp noExt fun (parenthesizeHsExpr GHC.appPrec arg)

varE :: SrcSpanAnnA -> GHC.RdrName -> LHsExpr GhcPs
varE loc rdr = L loc (HsVar noExtField (noLoc rdr))

parenE :: LHsExpr GhcPs -> LHsExpr GhcPs
parenE e@(L l _) = L l (HsPar noExt e)

var :: String -> GHC.RdrName
var = GHC.Unqual . OccName.mkVarOcc

tyVar :: String -> GHC.RdrName
tyVar = GHC.Unqual . OccName.mkTyVarOcc

tyCon :: String -> GHC.RdrName
tyCon = GHC.Unqual . OccName.mkTcOcc

vecE :: SrcSpanAnnA -> [LHsExpr GhcPs] -> LHsExpr GhcPs
vecE srcLoc = \case
  [] -> go srcLoc []
  as -> parenE $ go srcLoc as
  where
  go loc (e@(L l _):es) = L loc $ OpApp noExt e (varE l (thName '(:>))) (go loc es)
  go loc [] = varE loc (thName 'Nil)

tupE :: p ~ GhcPs => SrcSpanAnnA -> [LHsExpr p] -> LHsExpr p
tupE _ [ele] = ele
tupE loc elems = L loc $ ExplicitTuple noExt tupArgs GHC.Boxed
  where
#if __GLASGOW_HASKELL__ >= 902
    tupArgs = map (Present noExt) elems
#else
    tupArgs = map (\arg@(L l _) -> L l (Present noExt arg)) elems
#endif

unL :: Located a -> a
unL (L _ a) = a

-- | Get a ghc name from a TH name that's known to be unique.
thName :: TH.Name -> GHC.RdrName
thName nm =
  case Convert.thRdrNameGuesses nm of
    [name] -> name
    _      -> error "thName called on a non NameG Name"

-- | Make a type signature from a port description. Things without a concrete type (e.g. Signal a),
--   are given a type name based on the location of the port.
portTypeSigM :: (p ~ GhcPs, ?nms :: ExternalNames) => PortDescription PortName -> CircuitM (LHsType p)
portTypeSigM = \case
  Tuple ps -> tupT <$> mapM portTypeSigM ps
  Vec s ps -> vecT s <$> mapM portTypeSigM ps
  Ref (PortName loc fs) -> do
    L.use portVarTypes >>= \pvt ->
      case lookupUniqMap pvt fs of
        Nothing -> 
          let 
            -- GHC >= 9.2 interprets any type variable name starting with a "_" as
            -- a wildcard and throws an error suggesting a concrete type. To prevent
            -- this error from cropping up, we prefix it with "dflt" if we detect an
            -- underscore. Note that we see "_" in cases where the user wants to ignore
            -- a certain protocol, hence then name "dflt".
            s0 = GHC.unpackFS fs
            s1 | '_':_ <- s0 = "dflt" <> s0
               | otherwise   = s0
          in
            pure $ varT loc (s1 <> "Ty")
        Just (_sigLoc, sig) -> pure sig
  PortErr loc msgdoc -> do
    dflags <- GHC.getDynFlags
    unsafePerformIO . throwOneError $
      mkLongErrMsg dflags (locA loc) Outputable.alwaysQualify (Outputable.text "portTypeSig") msgdoc
  Lazy _ p -> portTypeSigM p
  SignalExpr (L l _) -> do
    n <- uniqueCounter <<+= 1
    pure $ (conT l (thName ''Signal)) `appTy` (varT l (genLocName l "dom")) `appTy` (varT l (genLocName l ("sig_" <> show n)))
  SignalPat (L l _) -> do
    n <- uniqueCounter <<+= 1
    pure $ (conT l (thName ''Signal)) `appTy` (varT l (genLocName l "dom")) `appTy` (varT l (genLocName l ("sig_" <> show n)))
  PortType _ p -> portTypeSigM p

-- | Generate a "unique" name by appending the location as a string.
genLocName :: SrcSpanAnnA -> String -> String
#if __GLASGOW_HASKELL__ >= 902
genLocName (locA -> GHC.RealSrcSpan rss _) prefix =
#elif __GLASGOW_HASKELL__ >= 900
genLocName (GHC.RealSrcSpan rss _) prefix =
#else
genLocName (GHC.RealSrcSpan rss) prefix =
#endif
  prefix <> "_" <>
    foldMap (\f -> show (f rss)) [srcSpanStartLine, srcSpanEndLine, srcSpanStartCol, srcSpanEndCol]
genLocName _ prefix = prefix

-- | Extract a simple lambda into inputs and body.
simpleLambda :: HsExpr GhcPs -> Maybe ([LPat GhcPs], LHsExpr GhcPs)
simpleLambda expr = do
  HsLam _ (MG _x alts _origin) <- Just expr
  L _ [L _ (Match _matchX _matchContext matchPats matchGr)] <- Just alts
  GRHSs _grX grHss _grLocalBinds <- Just matchGr
  [L _ (GRHS _ _ body)] <- Just grHss
  Just (matchPats, body)

-- | Create a simple let binding.
letE
  :: p ~ GhcPs
  => SrcSpanAnnA
  -- ^ location for top level let bindings
  -> [LSig p]
  -- ^ type signatures
  -> [LHsBind p]
  -- ^ let bindings
  -> LHsExpr p
  -- ^ final `in` expressions
  -> LHsExpr p
letE loc sigs binds expr = L loc (HsLet noExt localBinds expr)
  where
#if __GLASGOW_HASKELL__ >= 902
    localBinds :: HsLocalBinds GhcPs
    localBinds = HsValBinds noExt valBinds
#else
    localBinds :: LHsLocalBindsLR GhcPs GhcPs
    localBinds = L loc $ HsValBinds noExt valBinds
#endif

    valBinds :: HsValBindsLR GhcPs GhcPs
    valBinds = ValBinds noAnnSortKey hsBinds sigs

    hsBinds :: LHsBindsLR GhcPs GhcPs
    hsBinds = listToBag binds

-- | Simple construction of a lambda expression
lamE :: [LPat GhcPs] -> LHsExpr GhcPs -> LHsExpr GhcPs
lamE pats expr = noLoc $ HsLam noExtField mg
  where
    mg :: MatchGroup GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    mg = MG noExtField matches GHC.Generated

    matches :: GenLocated SrcSpanAnnL [GenLocated SrcSpanAnnA (Match GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))]
    matches = noLoc $ [singleMatch]

    singleMatch :: GenLocated SrcSpanAnnA (Match GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
    singleMatch = noLoc $ Match noExt LambdaExpr pats grHss

    grHss :: GRHSs GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    grHss = GRHSs emptyComments [grHs] $
#if __GLASGOW_HASKELL__ >= 902
      (EmptyLocalBinds noExtField)
#else
      (noLoc (EmptyLocalBinds noExtField))
#endif

    grHs :: GenLocated SrcSpan (GRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
    grHs = L noSrcSpan $ GRHS noExt [] expr

-- | Kinda hacky function to get a string name for named ports.
fromRdrName :: GHC.RdrName -> GHC.FastString
fromRdrName = \case
  GHC.Unqual occName -> mkFastString (OccName.occNameString occName)
  GHC.Orig _ occName -> mkFastString (OccName.occNameString occName)
  nm -> mkFastString (deepShowD nm)

-- Parsing -------------------------------------------------------------

-- | "parse" a circuit, i.e. convert it from ghc's ast to our representation of a circuit. This is
-- the expression following the 'circuit' keyword.
parseCircuit
  :: p ~ GhcPs
  => LHsExpr p
  -> CircuitM ()
parseCircuit = \case
  -- strip out parenthesis
  L _ (HsPar _ lexp) -> parseCircuit lexp

  -- a lambda to match the slave ports
  L _ (simpleLambda -> Just ([matchPats], body)) -> do
    circuitSlaves .= bindSlave matchPats
    circuitBody body

  -- a version without a lambda (i.e. no slaves)
  e -> circuitBody e

-- | The main part of a circuit expression. Either a do block or simple rearranging case.
circuitBody :: LHsExpr GhcPs -> CircuitM ()
circuitBody = \case
  -- strip out parenthesis
  L _ (HsPar _ lexp) -> circuitBody lexp

  L loc (HsDo _x _stmtContext (L _ (unsnoc -> Just (stmts, L finLoc finStmt)))) -> do
    circuitLoc .= loc
    mapM_ handleStmtM stmts

    case finStmt of
      BodyStmt _bodyX bod _idr _idr' ->
        case bod of
          -- special case for idC as the final statement, gives better type inferences and generates nicer
          -- code
#if __GLASGOW_HASKELL__ < 810
          L _ (HsArrApp _xapp (L _ (HsVar _ (L _ (GHC.Unqual occ)))) arg _ _)
            | OccName.occNameString occ == "idC" -> circuitMasters .= bindMaster arg
#else
          L _ (OpApp _ (L _ (HsVar _ (L _ (GHC.Unqual occ)))) (L _ op) port)
            | isFletching op
            , OccName.occNameString occ == "idC" -> do
                circuitMasters .= bindMaster port
#endif

          -- Otherwise create a binding and use that as the master. This is equivalent to changing
          --   c -< x
          -- into
          --   finalStmt <- c -< x
          --   idC -< finalStmt
          _ -> do
            let ref = Ref (PortName finLoc "final:stmt")
            bodyBinding (Just ref) (bod)
            circuitMasters .= ref

      stmt -> errM (locA finLoc) ("Unhandled final stmt " <> show (Data.toConstr stmt))

  -- the simple case without do notation
  L loc master -> do
    circuitLoc .= loc
    circuitMasters .= bindMaster (L loc master)

-- | Handle a single statement.
handleStmtM
  :: GenLocated SrcSpanAnnA (StmtLR GhcPs GhcPs (LHsExpr GhcPs))
  -> CircuitM ()
handleStmtM (L loc stmt) = case stmt of
#if __GLASGOW_HASKELL__ >= 902
  LetStmt _xlet letBind ->
#else
  LetStmt _xlet (L _ letBind) ->
#endif
    -- a regular let bindings
    case letBind of
      HsValBinds _ (ValBinds _ valBinds sigs) -> do
        circuitLets <>= bagToList valBinds
        circuitTypes <>= sigs
      _ -> errM (locA loc) ("Unhandled let statement" <> show (Data.toConstr letBind))
  BodyStmt _xbody body _idr _idr' ->
    bodyBinding Nothing body
#if __GLASGOW_HASKELL__ >= 900
  BindStmt _ bind body ->
#else
  BindStmt _xbody bind body _idr _idr' ->
#endif
    bodyBinding (Just $ bindSlave bind) body
  _ -> errM (locA loc) "Unhandled stmt"

-- | Turn patterns to the left of a @<-@ into a PortDescription.
bindSlave :: p ~ GhcPs => LPat p -> PortDescription PortName
bindSlave (L loc expr) = case expr of
  VarPat _ (L _ rdrName) -> Ref (PortName loc (fromRdrName rdrName))
  TuplePat _ lpat _ -> Tuple $ fmap bindSlave lpat
  ParPat _ lpat -> bindSlave lpat
#if __GLASGOW_HASKELL__ >= 902
  ConPat _ (L _ (GHC.Unqual occ)) (PrefixCon [] [lpat])
#elif __GLASGOW_HASKELL__ >= 900
  ConPat _ (L _ (GHC.Unqual occ)) (PrefixCon [lpat])
#else
  ConPatIn (L _ (GHC.Unqual occ)) (PrefixCon [lpat])
#endif
    | OccName.occNameString occ == "Signal" -> SignalPat lpat
  -- empty list is done as the constructor
#if __GLASGOW_HASKELL__ >= 900
  ConPat _ (L _ rdr) _
#else
  ConPatIn (L _ rdr) _
#endif
    | rdr == thName '[] -> Vec loc []
    | rdr == thName '() -> Tuple []
#if __GLASGOW_HASKELL__ < 810
  SigPat ty port -> PortType (hsSigWcType ty) (bindSlave port)
#elif __GLASGOW_HASKELL__ < 900
  SigPat _ port ty -> PortType (hsSigWcType ty) (bindSlave port)
#else
  SigPat _ port ty -> PortType (hsps_body ty) (bindSlave port)
#endif
  LazyPat _ lpat -> Lazy loc (bindSlave lpat)
  ListPat _ pats -> Vec loc (map bindSlave pats)
  pat ->
    PortErr loc
            (Err.mkLocMessageAnn
              Nothing
              Err.SevFatal
              (locA loc)
              (Outputable.text $ "Unhandled pattern " <> show (Data.toConstr pat))
              )

-- | Turn expressions to the right of a @-<@ into a PortDescription.
bindMaster :: LHsExpr GhcPs -> PortDescription PortName
bindMaster (L loc expr) = case expr of
  HsVar _xvar (L _vloc rdrName)
    | rdrName == thName '() -> Tuple []
    | rdrName == thName '[] -> Vec loc [] -- XXX: vloc?
    | otherwise -> Ref (PortName loc (fromRdrName rdrName)) -- XXX: vloc?
  HsApp _xapp (L _ (HsVar _ (L _ (GHC.Unqual occ)))) sig
    | OccName.occNameString occ == "Signal" -> SignalExpr sig
  ExplicitTuple _ tups _ -> let
#if __GLASGOW_HASKELL__ >= 902
    vals = fmap (\(Present _ e) -> e) tups
#else
    vals = fmap (\(L _ (Present _ e)) -> e) tups
#endif
    in Tuple $ fmap bindMaster vals
#if __GLASGOW_HASKELL__ >= 902
  ExplicitList _ exprs ->
#else
  ExplicitList _ _syntaxExpr exprs ->
#endif
    Vec loc $ fmap bindMaster exprs
#if __GLASGOW_HASKELL__ < 810
  HsArrApp _xapp (L _ (HsVar _ (L _ (GHC.Unqual occ)))) sig _ _
    | OccName.occNameString occ == "Signal" -> SignalExpr sig
  ExprWithTySig ty expr' -> PortType (hsSigWcType ty) (bindMaster expr')
  ELazyPat _ expr' -> Lazy loc (bindMaster expr')
#else
  -- XXX: Untested?
  HsProc _ _ (L _ (HsCmdTop _ (L _ (HsCmdArrApp _xapp (L _ (HsVar _ (L _ (GHC.Unqual occ)))) sig _ _))))
    | OccName.occNameString occ == "Signal" -> SignalExpr sig
  ExprWithTySig _ expr' ty -> PortType (hsSigWcType ty) (bindMaster expr')
#endif

  -- OpApp _xapp (L _ circuitVar) (L _ infixVar) appR -> k

  _ -> PortErr loc
    (Err.mkLocMessageAnn
      Nothing
      Err.SevFatal
      (locA loc)
      (Outputable.text $ "Unhandled expression " <> show (Data.toConstr expr))
      )

-- | Create a binding expression
bodyBinding
  :: Maybe (PortDescription PortName)
  -- ^ the bound variable, this can be Nothing if there is no @<-@ (a circuit with no slaves)
  -> GenLocated SrcSpanAnnA (HsExpr GhcPs)
  -- ^ the statement with an optional @-<@
  -> CircuitM ()
bodyBinding mInput lexpr@(L loc expr) = do
  case expr of
#if __GLASGOW_HASKELL__ < 810
    HsArrApp _xhsArrApp circuit port HsFirstOrderApp True ->
      circuitBinds <>= [Binding
        { bCircuit = circuit
        , bOut     = bindMaster port
        , bIn      = fromMaybe (Tuple []) mInput
        }]
#else
    OpApp _ circuit (L _ op) port | isFletching op -> do
      circuitBinds <>= [Binding
        { bCircuit = circuit
        , bOut     = bindMaster port
        , bIn      = fromMaybe (Tuple []) mInput
        }]
#endif

    _ -> case mInput of
      Nothing -> errM (locA loc) "standalone expressions are not allowed (are Arrows enabled?)"
      Just input -> circuitBinds <>= [Binding
        { bCircuit = lexpr
        , bOut     = Tuple []
        , bIn      = input
        }]

-- Checking ------------------------------------------------------------

data Dir = Slave | Master

checkCircuit :: p ~ GhcPs => CircuitM ()
checkCircuit = do
  slaves <- L.use circuitSlaves
  masters <- L.use circuitMasters
  binds <- L.use circuitBinds

  let portNames d = L.toListOf (L.cosmos . _Ref . L.to (f d))
      f :: Dir -> PortName -> (GHC.FastString, ([SrcSpanAnnA], [SrcSpanAnnA]))
      f Slave (PortName srcLoc portName) = (portName, ([srcLoc], []))
      f Master (PortName srcLoc portName) = (portName, ([], [srcLoc]))
      bindingNames = \b -> portNames Master (bOut b) <> portNames Slave (bIn b)
      topNames = portNames Slave slaves <> portNames Master masters
      nameMap = listToUniqMap_C mappend $ topNames <> concatMap bindingNames binds

  forM_ (nonDetUniqMapToList nameMap) \(name, occ) ->
    case occ of
      ([_], [_]) -> pure ()
      (ss, ms) -> do
        unless (head (unpackFS name) == '_') $ do
          when (null ms) $ errM (locA (head ss)) $ "Slave port " <> show name <> " has no associated master"
          when (null ss) $ errM (locA (head ms)) $ "Master port " <> show name <> " has no associated slave"
        -- would be nice to show locations of all occurrences here, not sure how to do that while
        -- keeping ghc api
        when (length ms > 1) $
          errM (locA (head ms)) $ "Master port " <> show name <> " defined " <> show (length ms) <> " times"
        when (length ss > 1) $
          errM (locA (head ss)) $ "Slave port " <> show name <> " defined " <> show (length ss) <> " times"

-- Creating ------------------------------------------------------------

bindWithSuffix :: (p ~ GhcPs, ?nms :: ExternalNames) => GHC.DynFlags -> String -> PortDescription PortName -> LPat p
bindWithSuffix dflags suffix = \case
  Tuple ps -> tildeP noSrcSpanA $ tupP $ fmap (bindWithSuffix dflags suffix) ps
  Vec s ps -> vecP s $ fmap (bindWithSuffix dflags suffix) ps
  Ref (PortName loc fs) -> varP loc (GHC.unpackFS fs <> suffix)
  PortErr loc msgdoc -> unsafePerformIO . throwOneError $
    mkLongErrMsg dflags (locA loc) Outputable.alwaysQualify (Outputable.text "Unhandled bind") msgdoc
  Lazy loc p -> tildeP loc $ bindWithSuffix dflags suffix p
#if __GLASGOW_HASKELL__ >= 902
  -- XXX: propagate location
  SignalExpr (L _ _) -> nlWildPat
#else 
  SignalExpr (L l _) -> L l (WildPat noExt)
#endif
  SignalPat lpat -> lpat
  PortType _ p -> bindWithSuffix dflags suffix p

data Direc = Fwd | Bwd

bindOutputs
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => GHC.DynFlags
  -> Direc
  -> PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LPat p
bindOutputs dflags Fwd slaves masters = noLoc $ conPatIn (noLoc (fwdBwdCon ?nms)) (InfixCon m2s s2m)
  where
  m2s = bindWithSuffix dflags "_Fwd" masters
  s2m = bindWithSuffix dflags "_Bwd" slaves
bindOutputs dflags Bwd slaves masters = noLoc $ conPatIn (noLoc (fwdBwdCon ?nms)) (InfixCon m2s s2m)
  where
  m2s = bindWithSuffix dflags "_Bwd" masters
  s2m = bindWithSuffix dflags "_Fwd" slaves

expWithSuffix :: p ~ GhcPs => String -> PortDescription PortName -> LHsExpr p
expWithSuffix suffix = \case
  Tuple ps -> tupE noSrcSpanA $ fmap (expWithSuffix suffix) ps
  Vec s ps -> vecE s $ fmap (expWithSuffix suffix) ps
  Ref (PortName loc fs)   -> varE loc (var $ GHC.unpackFS fs <> suffix)
  -- laziness only affects the pattern side
  Lazy _ p   -> expWithSuffix suffix p
  PortErr _ _ -> error "expWithSuffix PortErr!"
  SignalExpr lexpr -> lexpr
  SignalPat (L l _) -> tupE l []
  PortType _ p -> expWithSuffix suffix p

createInputs
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => Direc
  -> PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LHsExpr p
createInputs Fwd slaves masters = noLoc $ OpApp noExt s2m (varE noSrcSpanA (fwdBwdCon ?nms)) m2s
  where
  m2s = expWithSuffix "_Bwd" masters
  s2m = expWithSuffix "_Fwd" slaves
createInputs Bwd slaves masters = noLoc $ OpApp noExt s2m (varE noSrcSpanA (fwdBwdCon ?nms)) m2s
  where
  m2s = expWithSuffix "_Fwd" masters
  s2m = expWithSuffix "_Bwd" slaves

decFromBinding :: (p ~ GhcPs, ?nms :: ExternalNames) => GHC.DynFlags -> Int -> Binding (LHsExpr p) PortName -> HsBind p
decFromBinding dflags i Binding {..} = do
  let bindPat  = bindOutputs dflags Bwd bIn bOut
      inputExp = createInputs Fwd bOut bIn
      bod = varE noSrcSpanA (var $ "run" <> show i) `appE` bCircuit `appE` inputExp
   in patBind bindPat bod

patBind :: LPat GhcPs -> LHsExpr GhcPs -> HsBind GhcPs
patBind lhs expr = PatBind noExt lhs rhs ([], [])
  where
    rhs :: GRHSs GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    rhs = GRHSs emptyComments [gr] $ 
#if __GLASGOW_HASKELL__ >= 902
      EmptyLocalBinds noExtField
#else
      noLoc (EmptyLocalBinds noExtField)
#endif

    gr :: GenLocated SrcSpan (GRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
    gr  = L (locA (getLoc expr)) (GRHS noExt [] expr)

circuitConstructor :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsExpr GhcPs
circuitConstructor loc = varE loc (circuitCon ?nms)

runCircuitFun :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsExpr GhcPs
runCircuitFun loc = varE loc (runCircuitName ?nms)

constVar :: SrcSpanAnnA -> LHsExpr GhcPs
constVar loc = varE loc (thName 'const)

deepShowD :: Data.Data a => a -> String
deepShowD a = show (Data.toConstr a) <>
  -- " (" <> (unwords . fst) (SYB.gmapM (\x -> ([show $ Data.toConstr x], x)) a) <> ")"
  " (" <> (unwords . fst) (SYB.gmapM (\x -> ([deepShowD x], x)) a) <> ")"

unsnoc :: [a] -> Maybe ([a], a)
unsnoc [] = Nothing
unsnoc [x] = Just ([], x)
unsnoc (x:xs) = Just (x:a, b)
    where Just (a,b) = unsnoc xs

hsFunTy :: (p ~ GhcPs) => LHsType p -> LHsType p -> HsType p
hsFunTy =
  HsFunTy noExt
#if __GLASGOW_HASKELL__ >= 900
    (HsUnrestrictedArrow GHC.NormalSyntax)
#endif

arrTy :: p ~ GhcPs => LHsType p -> LHsType p -> LHsType p
arrTy a b = noLoc $ hsFunTy (parenthesizeHsType GHC.funPrec a) (parenthesizeHsType GHC.funPrec b)

varT :: SrcSpanAnnA -> String -> LHsType GhcPs
varT loc nm = L loc (HsTyVar noExt NotPromoted (noLoc (tyVar nm)))

conT :: SrcSpanAnnA -> GHC.RdrName -> LHsType GhcPs
conT loc nm = L loc (HsTyVar noExt NotPromoted (noLoc nm))

circuitTy :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsType p -> LHsType p -> LHsType p
circuitTy a b = conT noSrcSpanA (circuitTyCon ?nms) `appTy` a `appTy` b

circuitTTy :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsType p -> LHsType p -> LHsType p
circuitTTy a b = conT noSrcSpanA (circuitTTyCon ?nms) `appTy` a `appTy` b

-- a b -> (Circuit a b -> CircuitT a b)
mkRunCircuitTy :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsType p -> LHsType p -> LHsType p
mkRunCircuitTy a b = noLoc $ hsFunTy (circuitTy a b) (circuitTTy a b)

-- a b -> (CircuitT a b -> Circuit a b)
mkCircuitTy :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsType p -> LHsType p -> LHsType p
mkCircuitTy a b = noLoc $ hsFunTy (circuitTTy a b) (circuitTy a b)

-- perhaps this should happen on construction
gatherTypes
  :: p ~ GhcPs
  => PortDescription PortName
  -> CircuitM ()
gatherTypes = L.traverseOf_ L.cosmos addTypes
  where
    addTypes = \case
      PortType ty (Ref (PortName loc fs)) -> 
        portVarTypes %= \pvt -> alterUniqMap (const (Just (loc, ty))) pvt fs
      PortType ty p -> portTypes <>= [(ty, p)]
      _             -> pure ()

tyEq :: LHsType GhcPs -> LHsType GhcPs -> LHsType GhcPs
tyEq a b = noLoc $ HsOpTy noExtField a (noLoc eqTyCon_RDR) b
-- eqTyCon is a special name that has to be exactly correct for ghc to recognise it. In 8.6 this
-- lives in PrelNames and is called eqTyCon_RDR, in later ghcs it's from TysWiredIn.

-- Final construction --------------------------------------------------

circuitQQExpM
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => CircuitM (LHsExpr p)
circuitQQExpM = do
  checkCircuit

  dflags <- GHC.getDynFlags
  binds <- L.use circuitBinds
  lets <- L.use circuitLets
  letTypes <- L.use circuitTypes
  slaves <- L.use circuitSlaves
  masters <- L.use circuitMasters

  -- Construction of the circuit expression
  let decs = concat
        [ lets
        , imap (\i -> noLoc . decFromBinding dflags i) binds
        ]
  let pats = bindOutputs dflags Fwd masters slaves
      res  = createInputs Bwd slaves masters

      body :: LHsExpr GhcPs
      body = letE noSrcSpanA letTypes decs res

  -- see [inference-helper]
  mapM_
    (\(Binding _ outs ins) -> gatherTypes outs >> gatherTypes ins)
    binds
  mapM_ gatherTypes [masters, slaves]

  slavesTy <- portTypeSigM slaves
  mastersTy <- portTypeSigM masters
  let mkRunTy bind =
        mkRunCircuitTy <$>
          (portTypeSigM (bOut bind)) <*>
          (portTypeSigM (bIn bind))
  bindTypes <- mapM mkRunTy binds
  let runCircuitsType =
        noLoc (HsParTy noExt (tupT bindTypes `arrTy` circuitTTy slavesTy mastersTy))
          `arrTy` circuitTy slavesTy mastersTy

  allTypes <- L.use portTypes

  context <- mapM (\(ty, p) -> tyEq <$> portTypeSigM p <*> pure ty) allTypes

  -- the full signature
  loc <- L.use circuitLoc
  let inferenceHelperName = genLocName loc "inferenceHelper"
      inferenceSig :: LHsSigType GhcPs
#if __GLASGOW_HASKELL__ >= 902
      inferenceSig = noLoc $ 
        HsSig
          noExtField
          (HsOuterImplicit noExtField)
          (noLoc $ HsQualTy noExtField (Just (noLoc context)) runCircuitsType)
#else
      inferenceSig = HsIB noExt (noLoc $ HsQualTy noExt (noLoc context) runCircuitsType)
#endif

      inferenceHelperTy =
        TypeSig noExt
          [noLoc (var inferenceHelperName)]
          (HsWC noExtField inferenceSig)

  let numBinds = length binds
      runCircuitExprs = lamE [varP noSrcSpanA "f"] $
        circuitConstructor noSrcSpanA `appE`
          noLoc (HsPar noExt
          (varE noSrcSpanA (var "f") `appE` tupE noSrcSpanA (replicate numBinds (runCircuitFun noSrcSpanA))))
      runCircuitBinds = tupP $ map (\i -> varP noSrcSpanA ("run" <> show i)) [0 .. numBinds-1]

  let c = letE noSrcSpanA
            [noLoc inferenceHelperTy]
            [noLoc $ patBind (varP noSrcSpanA inferenceHelperName) (runCircuitExprs)]
            (varE noSrcSpanA (var inferenceHelperName) `appE` lamE [runCircuitBinds, pats] body)
  -- ppr c
  pure c

  -- pure $ varE noSrcSpan (var "undefined")

-- [inference-helper]
-- The inference helper constructs the circuit and provides all the `runCircuit`s with the types
-- matching the structure of the port expressions. This way we can enforce that ports 'keep the
-- same type' which normally gets lost when deconstructing and reconstructing types. It also means
-- that we can add type annotations of the ports as a context to this helper function. For example
--
-- swapIC c = circuit $ \(a :: Int, b) -> do
--   a' <- c -< a
--   b' <- c -< b
--   idC -< (b',a')
--
-- will produce the helper
--
-- inferenceHelper ::
--   aTy ~ Int =>
--   -> (   (Circuit aTy a'Ty -> CircuitT aTy a'Ty)
--       -> (Circuit bTy b'Ty -> CircuitT bTy b'Ty)
--       -> CircuitT (aTy, bTy) (b'Ty, a'Ty)
--      ) -> CircuitT (aTy, bTy) (b'Ty, a'Ty)
-- inferenceHelper = \f -> Circuit (f runCircuit runCircuit)


grr :: MonadIO m => OccName.NameSpace -> m ()
grr nm
  | nm == OccName.tcName = liftIO $ putStrLn "tcName"
  | nm == OccName.clsName = liftIO $ putStrLn "clsName"
  | nm == OccName.tcClsName = liftIO $ putStrLn "tcClsName"
  | nm == OccName.dataName = liftIO $ putStrLn "dataName"
  | nm == OccName.varName = liftIO $ putStrLn "varName"
  | nm == OccName.tvName = liftIO $ putStrLn "tvName"
  | otherwise = liftIO $ putStrLn "I dunno"

completeUnderscores :: CircuitM ()
completeUnderscores = do
  binds <- L.use circuitBinds
  masters <- L.use circuitMasters
  slaves <- L.use circuitSlaves
  let addDef :: String -> PortDescription PortName -> CircuitM ()
      addDef suffix = \case
        Ref (PortName loc (unpackFS -> name@('_':_))) -> do
          let bind = patBind (varP loc (name <> suffix)) (varE loc (thName 'def))
          circuitLets <>= [L loc bind]

        _ -> pure ()
      addBind :: Binding exp PortName -> CircuitM ()
      addBind (Binding _ bOut bIn) = do
        L.traverseOf_ L.cosmos (addDef "_Fwd") bOut
        L.traverseOf_ L.cosmos (addDef "_Bwd") bIn
  mapM_ addBind binds
  addBind (Binding undefined masters slaves)


-- | Transform declarations in the module by converting circuit blocks.
transform
    :: (?nms :: ExternalNames)
    => Bool
#if __GLASGOW_HASKELL__ >= 900
    -> GHC.Located HsModule
    -> GHC.Hsc (GHC.Located HsModule)
#else
    -> GHC.Located (HsModule GhcPs)
    -> GHC.Hsc (GHC.Located (HsModule GhcPs))
#endif
transform debug = SYB.everywhereM (SYB.mkM transform') where
  transform' :: LHsExpr GhcPs -> GHC.Hsc (LHsExpr GhcPs)

  -- the circuit keyword directly applied (either with parenthesis or with BlockArguments)
  transform' (L _ (HsApp _xapp (L _ circuitVar) lappB))
    | isCircuitVar circuitVar = runCircuitM $ do
        x <- parseCircuit lappB >> completeUnderscores >> circuitQQExpM
        when debug $ ppr x
        pure x

  -- `circuit $` application
  transform' (L _ (OpApp _xapp c@(L _ circuitVar) (L _ infixVar) appR))
    | isDollar infixVar && dollarChainIsCircuit circuitVar = do
        runCircuitM $ do
          x <- parseCircuit appR >> completeUnderscores >> circuitQQExpM
          when debug $ ppr x
          pure (dollarChainReplaceCircuit x c)

  transform' e = pure e

-- | check if circuit is applied via `a $ chain $ of $ dollars`.
dollarChainIsCircuit :: HsExpr GhcPs -> Bool
dollarChainIsCircuit = \case
  HsVar _ (L _ v)                             -> v == GHC.mkVarUnqual "circuit"
  OpApp _xapp _appL (L _ infixVar) (L _ appR) -> isDollar infixVar && dollarChainIsCircuit appR
  _                                           -> False

-- | Replace the circuit if it's part of a chain of `$`.
dollarChainReplaceCircuit :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
dollarChainReplaceCircuit circuitExpr (L loc app) = case app of
  HsVar _ (L _loc v)
    -> if v == GHC.mkVarUnqual "circuit"
         then circuitExpr
         else error "dollarChainAddCircuit: not a circuit"
  OpApp xapp appL (L infixLoc infixVar) appR
    -> L loc $ OpApp xapp appL (L infixLoc infixVar) (dollarChainReplaceCircuit circuitExpr appR)
  t -> error $ "dollarChainAddCircuit unhandled case " <> showC t

-- | The plugin for circuit notation.
plugin :: GHC.Plugin
plugin = mkPlugin defExternalNames

-- | Make a plugin with custom external names
mkPlugin :: ExternalNames -> GHC.Plugin
mkPlugin nms = GHC.defaultPlugin
  { GHC.parsedResultAction = let ?nms = nms in pluginImpl
    -- Mark plugin as 'pure' to prevent recompilations.
  , GHC.pluginRecompile = \_cliOptions -> pure GHC.NoForceRecompile
  }

warningMsg :: Outputable.SDoc -> GHC.Hsc ()
warningMsg sdoc = do
  dflags <- GHC.getDynFlags
#if __GLASGOW_HASKELL__ >= 902
  logger <- GHC.getLogger
  liftIO $ Err.warningMsg logger dflags sdoc
#else
  liftIO $ Err.warningMsg dflags sdoc
#endif

-- | The actual implementation.
pluginImpl :: (?nms :: ExternalNames) => [GHC.CommandLineOption] -> GHC.ModSummary -> GHC.HsParsedModule -> GHC.Hsc GHC.HsParsedModule
pluginImpl cliOptions _modSummary m = do
    -- cli options are activated by -fplugin-opt=CircuitNotation:debug
    debug <- case cliOptions of
      []        -> pure False
      ["debug"] -> pure True
      _ -> do 
        warningMsg $ Outputable.text $ "CircuitNotation: unknown cli options " <> show cliOptions
        pure False
    hpm_module' <- do
      transform debug (GHC.hpm_module m)
    let module' = m { GHC.hpm_module = hpm_module' }
    return module'

-- Debugging functions -------------------------------------------------

ppr :: GHC.Outputable a => a -> CircuitM ()
ppr a = do
  dflags <- GHC.getDynFlags
  liftIO $ putStrLn (GHC.showPpr dflags a)

showC :: Data.Data a => a -> String
showC a = show (typeOf a) <> " " <> show (Data.toConstr a)

-- ppp :: MonadIO m => String -> m ()
-- ppp s = case SP.parseValue s of
--   Just a -> valToStr a

-- Names ---------------------------------------------------------------

-- | Collection of names external to circuit-notation.
data ExternalNames = ExternalNames
  { circuitCon :: GHC.RdrName
  , circuitTyCon :: GHC.RdrName
  , circuitTTyCon :: GHC.RdrName
  , runCircuitName :: GHC.RdrName
  , fwdBwdCon :: GHC.RdrName
  }

defExternalNames :: ExternalNames
defExternalNames = ExternalNames
  { circuitCon = GHC.Unqual (OccName.mkDataOcc "Circuit")
  , circuitTyCon = GHC.Unqual (OccName.mkTcOcc "Circuit")
  , circuitTTyCon = GHC.Unqual (OccName.mkTcOcc "CircuitT")
  , runCircuitName = GHC.Unqual (OccName.mkVarOcc "runCircuit")
  , fwdBwdCon = GHC.Unqual (OccName.mkDataOcc ":->")
  }
