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
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE ViewPatterns               #-}

{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CircuitNotation
  ( plugin
  , mkPlugin
  , thName
  , ExternalNames (..)
  , defExternalNames
  , Direction(..)
  ) where

-- base
import           Control.Exception
import qualified Data.Data              as Data
import           Data.Default
import           Data.List              (partition, sort, sortOn)
import           Data.Maybe             (fromMaybe)
import           System.IO.Unsafe
import           Data.Typeable

-- containers
import qualified Data.Map.Strict        as Map
import qualified Data.Set               as Set

-- ghc
import qualified Language.Haskell.TH    as TH
import qualified GHC

import           GHC.Types.SourceError  (throwOneError)
import qualified GHC.Driver.Env         as GHC
import qualified GHC.Types.SourceText   as GHC
import qualified GHC.Types.SourceError  as GHC
import qualified GHC.Driver.Ppr         as GHC

import           GHC.Data.Bag
import           GHC.Data.FastString       (mkFastString, unpackFS)
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

import GHC.Driver.Errors.Ppr () -- instance Diagnostic GhcMessage

import qualified GHC.Driver.Config.Diagnostic as GHC
import qualified GHC.Driver.Errors.Types      as GHC
import qualified GHC.Utils.Logger             as GHC
#if __GLASGOW_HASKELL__ < 910
import qualified GHC.Parser.PostProcess       as GHC
#else
import GHC.Parser.PostProcess () -- instances
#endif

import qualified GHC.ThToHs             as Convert
import           GHC.Hs
  hiding (locA)

import           GHC.Builtin.Types      (eqTyCon_RDR)

import "ghc" GHC.Types.Unique.Map

#if __GLASGOW_HASKELL__ < 908
import GHC.Types.Unique.Map.Extra
#endif

-- clash-prelude
import Clash.Prelude (Vec((:>), Nil), bundle, unbundle)
import qualified Clash.Signal.Delayed.Bundle as DBundle

-- lens
import qualified Control.Lens           as L
import           Control.Lens.Operators

-- mtl
import           Control.Monad
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
#if __GLASGOW_HASKELL__ < 910
type MsgDoc = Outputable.SDoc

locA :: SrcAnn a -> SrcSpan
locA = GHC.locA

noAnnSortKey :: AnnSortKey
noAnnSortKey = NoAnnSortKey
#else
type MsgDoc = Outputable.SDoc

locA :: EpAnn a -> SrcSpan
locA = GHC.locA

noAnnSortKey :: AnnSortKey a
noAnnSortKey = NoAnnSortKey
#endif

type ErrMsg = Err.MsgEnvelope GHC.GhcMessage

sevFatal :: Err.MessageClass
sevFatal = Err.MCFatal

#if __GLASGOW_HASKELL__ >= 910
noExt :: NoAnn a => a
noExt = noAnn
#else
noExt :: EpAnn ann
noExt = EpAnnNotUsed
#endif

#if __GLASGOW_HASKELL__ < 910
pattern HsParP :: LHsExpr p -> HsExpr p
pattern HsParP e <- HsPar _ _ e _

pattern ParPatP :: LPat p -> Pat p
pattern ParPatP p <- ParPat _ _ p _
#else
pattern HsParP :: LHsExpr p -> HsExpr p
pattern HsParP e <- HsPar _ e

pattern ParPatP :: LPat p -> Pat p
pattern ParPatP p <- ParPat _ p
#endif

type PrintUnqualified = Outputable.NamePprCtx

mkErrMsg :: GHC.DynFlags -> SrcSpan -> PrintUnqualified -> Outputable.SDoc -> ErrMsg
-- Check the documentation of
-- `GHC.Driver.Errors.Types.ghcUnkownMessage` for some background on
-- why plugins should use this generic message constructor.
mkErrMsg _ locn unqual =
    Err.mkErrorMsgEnvelope locn unqual
  . GHC.ghcUnknownMessage
  . Err.mkPlainError Err.noHints

mkLongErrMsg :: GHC.DynFlags -> SrcSpan -> PrintUnqualified -> Outputable.SDoc -> Outputable.SDoc -> ErrMsg
mkLongErrMsg _ locn unqual msg extra =
    Err.mkErrorMsgEnvelope locn unqual
  $ GHC.ghcUnknownMessage
  $ Err.mkDecoratedError Err.noHints [msg, extra]

-- Types ---------------------------------------------------------------

-- | The name given to a 'port', i.e. the name of a variable either to the left of a '<-' or to the
--   right of a '-<'.
data PortName = PortName SrcSpanAnnA GHC.FastString
  deriving (Eq)

instance Show PortName where
  show (PortName _ fs) = GHC.unpackFS fs

-- | Which keyword marked a port. @Signal@ and @Fwd@ are bus-level (and
-- interchangeable): they bind/inject the raw forward channel. @SignalV@ and
-- @FwdV@ mark the /value/ boundary, binding or injecting the per-cycle
-- value: @SignalV@ asserts the bus /is/ a 'Signal' (generating the concrete
-- @SigTag@, which drives type inference) while @FwdV@ samples the forward
-- channel of any signal-like bus (generating the class-constrained
-- @FwdTag@, which requires the bus type to be determined by context).
data SigMarker = SignalMarker | FwdMarker | SignalVMarker | FwdVMarker | DSignalVMarker

-- | Is this marker a value boundary (@SignalV@/@FwdV@/@DSignalV@)?
isValueMarker :: SigMarker -> Bool
isValueMarker = \case
  SignalVMarker  -> True
  FwdVMarker     -> True
  DSignalVMarker -> True
  _              -> False

-- | Value groups come in two flavors, lifted with the matching bundle:
-- plain signal values (@SignalV@/@FwdV@) and delayed signal values
-- (@DSignalV@). The flavors cannot meet in one group.
data GroupFlavor = SignalGroup | DSignalGroup deriving Eq

valueMarkerFlavor :: SigMarker -> GroupFlavor
valueMarkerFlavor = \case
  DSignalVMarker -> DSignalGroup
  _              -> SignalGroup

data PortDescription a
    = Tuple [PortDescription a]
    | Vec SrcSpanAnnA [PortDescription a]
    | Ref a
    | RefMulticast a
    | Lazy SrcSpanAnnA (PortDescription a)
    | FwdExpr SigMarker (LHsExpr GhcPs)
    | FwdPat SigMarker (LPat GhcPs)
    | SigTagExpr SigMarker (LHsExpr GhcPs)
    -- ^ generated for value markers: a value-boundary bus expression, tagged
    -- with @SigTag@/@FwdTag@ according to the marker
    | SigTagPat SigMarker (LPat GhcPs)
    -- ^ generated for value markers: a value-boundary bus pattern, tagged with
    -- @SigTag@/@FwdTag@ according to the marker
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
    , _circuitCompletes :: [dec]
    -- ^ generated bindings that complete underscored ports
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
        , _circuitCompletes = []
        , _circuitBinds = []
        , _circuitMasters = Tuple []
        , _portVarTypes = emptyUniqMap
        , _portTypes = []
        , _uniqueCounter = 1
        , _circuitLoc = noSrcSpanA
        }
  (a, s) <- runStateT m emptyCircuitState
  let errs = _cErrors s
  unless (isEmptyBag errs) $ liftIO . throwIO $ GHC.mkSrcErr $ Err.mkMessages errs
  pure a

mkLocMessage :: Err.MessageClass -> SrcSpan -> Outputable.SDoc -> Outputable.SDoc
mkLocMessage = Err.mkLocMessage

errM :: SrcSpan -> String -> CircuitM ()
errM loc msg = do
  dflags <- GHC.getDynFlags
  let errMsg = mkLocMessage sevFatal loc (Outputable.text msg)
  cErrors %= consBag (mkErrMsg dflags loc Outputable.alwaysQualify errMsg)

-- ghc helpers ---------------------------------------------------------

-- It's very possible that most of these are already in the ghc library in some form. It's not the
-- easiest library to discover these kind of functions.

conPatIn :: GenLocated SrcSpanAnnN GHC.RdrName -> HsConPatDetails GhcPs -> Pat GhcPs
conPatIn loc con = ConPat noExt loc con

#if __GLASGOW_HASKELL__ >= 910
noEpAnn :: NoAnn ann => GenLocated SrcSpan e -> GenLocated (EpAnn ann) e
noEpAnn (L l e) = L (EpAnn (spanAsAnchor l) noAnn emptyComments) e

noLoc :: NoAnn ann => e -> GenLocated (EpAnn ann) e
noLoc = noEpAnn . GHC.noLoc
#else
noEpAnn :: GenLocated SrcSpan e -> GenLocated (SrcAnn ann) e
noEpAnn (L l e) = L (SrcSpanAnn noExt l) e

noLoc :: e -> GenLocated (SrcAnn ann) e
noLoc = noEpAnn . GHC.noLoc
#endif

tupP :: p ~ GhcPs => [LPat p] -> LPat p
tupP [pat] = pat
tupP pats = noLoc $ TuplePat noExt pats GHC.Boxed

vecP :: (?nms :: ExternalNames) => SrcSpanAnnA -> [LPat GhcPs] -> LPat GhcPs
vecP srcLoc = \case
  [] -> go []
#if __GLASGOW_HASKELL__ < 910
  as -> L srcLoc $ ParPat noExt pL (go as) pR
  where
  pL = L (GHC.mkTokenLocation $ locA srcLoc) HsTok
  pR = L (GHC.mkTokenLocation $ locA srcLoc) HsTok
#else
  as -> L srcLoc $ ParPat (pL,pR) (go as)
  where
  pL = EpTok $ spanAsAnchor $ locA srcLoc
  pR = EpTok $ spanAsAnchor $ locA srcLoc
#endif
  go :: [LPat GhcPs] -> LPat GhcPs
  go (p@(L l0 _):pats) =
    let l1 = l0 `seq` noSrcSpanA
    in
      L srcLoc $ conPatIn (L l1 (consPat ?nms)) (InfixCon p (go pats))
  go [] = L srcLoc $ WildPat noExtField

varP :: SrcSpanAnnA -> String -> LPat GhcPs
varP loc nm = L loc $ VarPat noExtField (noLoc $ var nm)

tildeP :: SrcSpanAnnA -> LPat GhcPs -> LPat GhcPs
tildeP loc lpat = L loc (LazyPat noExt lpat)

hsBoxedTuple :: GHC.HsTupleSort
hsBoxedTuple = HsBoxedOrConstraintTuple

tupT :: [LHsType GhcPs] -> LHsType GhcPs
tupT [ty] = ty
tupT tys = noLoc $ HsTupleTy noExt hsBoxedTuple tys

vecT :: SrcSpanAnnA -> [LHsType GhcPs] -> LHsType GhcPs
vecT s [] = L s $ HsParTy noExt (conT s (thName ''Vec) `appTy` tyNum s 0 `appTy` (varT s (genLocName s "vec")))
vecT s tys@(ty:_) = L s $ HsParTy noExt (conT s (thName ''Vec) `appTy` tyNum s (length tys) `appTy` ty)

tyNum :: SrcSpanAnnA -> Int -> LHsType GhcPs
tyNum s i = L s (HsTyLit noExtField (HsNumTy GHC.NoSourceText (fromIntegral i)))

appTy :: LHsType GhcPs -> LHsType GhcPs -> LHsType GhcPs
appTy a b = noLoc (HsAppTy noExtField a (parenthesizeHsType GHC.appPrec b))

appE :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
appE fun arg = L noSrcSpanA $ HsApp
#if __GLASGOW_HASKELL__ >= 910
  noExtField
#else
  noAnn
#endif
  fun (parenthesizeHsExpr GHC.appPrec arg)

varE :: SrcSpanAnnA -> GHC.RdrName -> LHsExpr GhcPs
varE loc rdr = L loc (HsVar noExtField (noLoc rdr))

parenE :: LHsExpr GhcPs -> LHsExpr GhcPs
#if __GLASGOW_HASKELL__ < 910
parenE e@(L l _) = L l (HsPar noExt pL e pR)
  where
  pL = L (GHC.mkTokenLocation $ locA l) HsTok
  pR = L (GHC.mkTokenLocation $ locA l) HsTok
#else
parenE e@(L l _) = L l (HsPar (pL,pR) e)
  where
  pL = EpTok $ spanAsAnchor $ locA l
  pR = EpTok $ spanAsAnchor $ locA l
#endif

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
  go loc (e@(L l _):es) = L loc $ OpApp
#if __GLASGOW_HASKELL__ >= 912
    noExtField
#else
    noExt
#endif
    e (varE l (thName '(:>))) (go loc es)
  go loc [] = varE loc (thName 'Nil)

tupE :: p ~ GhcPs => SrcSpanAnnA -> [LHsExpr p] -> LHsExpr p
tupE _ [ele] = ele
tupE loc elems = L loc $ ExplicitTuple noExt tupArgs GHC.Boxed
  where
    tupArgs = map
#if __GLASGOW_HASKELL__ >= 910
      (Present noExtField)
#else
      (Present noAnn)
#endif
      elems

unL :: Located a -> a
unL (L _ a) = a

-- | Get a ghc name from a TH name that's known to be unique.
thName :: TH.Name -> GHC.RdrName
thName nm =
  case Convert.thRdrNameGuesses nm of
    [name] -> name
    _      -> error "thName called on a non NameG Name"

-- | Generate a "unique" name by appending the location as a string.
genLocName :: SrcSpanAnnA -> String -> String
genLocName (locA -> GHC.RealSrcSpan rss _) prefix =
  prefix <> "_" <>
    foldMap (\f -> show (f rss)) [srcSpanStartLine, srcSpanEndLine, srcSpanStartCol, srcSpanEndCol]
genLocName _ prefix = prefix

-- | Extract a simple lambda into inputs and body.
simpleLambda :: HsExpr GhcPs -> Maybe ([LPat GhcPs], LHsExpr GhcPs)
simpleLambda expr = do
#if __GLASGOW_HASKELL__ < 910
  HsLam _ (MG _x alts) <- Just expr
#else
  HsLam _ _ (MG _x alts) <- Just expr
#endif
#if __GLASGOW_HASKELL__ >= 912
  L _ [L _ (Match _matchX _matchContext (L _ matchPats) matchGr)] <- Just alts
#else
  L _ [L _ (Match _matchX _matchContext matchPats matchGr)] <- Just alts
#endif
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
letE loc sigs binds expr =
#if __GLASGOW_HASKELL__ < 908
    L loc (HsLet noExt tkLet localBinds tkIn expr)
#elif __GLASGOW_HASKELL__ < 910
    L loc (HsLet noExt tkLet localBinds tkIn expr)
#else
    L loc (HsLet (tkLet,tkIn) localBinds expr)
#endif
  where
    localBinds :: HsLocalBinds GhcPs
    localBinds = HsValBinds noExt valBinds

#if __GLASGOW_HASKELL__ >= 910
    tkLet = EpTok $ spanAsAnchor $ locA loc
    tkIn  = EpTok $ spanAsAnchor $ locA loc
#else
    tkLet = L (GHC.mkTokenLocation $ locA loc) HsTok
    tkIn  = L (GHC.mkTokenLocation $ locA loc) HsTok
#endif

    valBinds :: HsValBindsLR GhcPs GhcPs
    valBinds = ValBinds noAnnSortKey hsBinds sigs

    hsBinds :: LHsBindsLR GhcPs GhcPs
#if __GLASGOW_HASKELL__ >= 912
    hsBinds = binds
#else
    hsBinds = listToBag binds
#endif

-- | Simple construction of a lambda expression
lamE :: [LPat GhcPs] -> LHsExpr GhcPs -> LHsExpr GhcPs
lamE pats expr =
#if __GLASGOW_HASKELL__ >= 910
    noLoc $ HsLam noExt LamSingle mg
#else
    noLoc $ HsLam noExtField mg
#endif
  where
    mg :: MatchGroup GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
#if __GLASGOW_HASKELL__ < 908
    mg = MG GHC.Generated matches
#elif __GLASGOW_HASKELL__ < 910
    mg = MG (GHC.Generated GHC.DoPmc) matches
#else
    mg = MG (GHC.Generated GHC.OtherExpansion GHC.DoPmc) matches
#endif

#if __GLASGOW_HASKELL__ >= 912
    matches :: XRec GhcPs [LMatch GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))]
    matches = noLoc [singleMatch]
#else
    matches :: GenLocated SrcSpanAnnL [GenLocated SrcSpanAnnA (Match GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))]
    matches = noLoc $ [singleMatch]
#endif

    singleMatch :: GenLocated SrcSpanAnnA (Match GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
#if __GLASGOW_HASKELL__ >= 912
    singleMatch = noLoc $ Match noExtField (LamAlt LamSingle) (L (EpaSpan noSrcSpan) pats) grHss
#elif __GLASGOW_HASKELL__ >= 910
    singleMatch = noLoc $ Match noExt (LamAlt LamSingle) pats grHss
#else
    singleMatch = noLoc $ Match noExt LambdaExpr pats grHss
#endif

    grHss :: GRHSs GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    grHss = GRHSs emptyComments [grHs] $
      (EmptyLocalBinds noExtField)

    grHs :: LGRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    grHs =  L noSrcSpanA $ GRHS noExt [] expr

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
  L _ (HsParP lexp) -> parseCircuit lexp

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
  L _ (HsParP lexp) -> circuitBody lexp

  L loc (HsDo _x _stmtContext (L _ (unsnoc -> Just (stmts, L finLoc finStmt)))) -> do
    circuitLoc .= loc
    mapM_ handleStmtM stmts

    case finStmt of
      BodyStmt _bodyX bod _idr _idr' ->
        case bod of
          -- special case for idC as the final statement, gives better type inferences and generates nicer
          -- code
          L _ (OpApp _ (L _ (HsVar _ (L _ (GHC.Unqual occ)))) (L _ op) port)
            | isFletching op
            , OccName.occNameString occ == "idC" -> do
                circuitMasters .= bindMaster port

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
  LetStmt _xlet letBind ->
    -- a regular let bindings
    case letBind of
      HsValBinds _ (ValBinds _ valBinds sigs) -> do
#if __GLASGOW_HASKELL__ >= 912
        circuitLets <>= valBinds
#else
        circuitLets <>= bagToList valBinds
#endif
        circuitTypes <>= sigs
      _ -> errM (locA loc) ("Unhandled let statement" <> show (Data.toConstr letBind))
  BodyStmt _xbody body _idr _idr' ->
    bodyBinding Nothing body
  BindStmt _ bind body ->
    bodyBinding (Just $ bindSlave bind) body
  _ -> errM (locA loc) "Unhandled stmt"

-- | Turn patterns to the left of a @<-@ into a PortDescription.
bindSlave :: p ~ GhcPs => LPat p -> PortDescription PortName
bindSlave (L loc expr) = case expr of
  VarPat _ (L _ rdrName) -> Ref (PortName loc (fromRdrName rdrName))
  TuplePat _ lpat _ -> Tuple $ fmap bindSlave lpat
  ParPatP lpat -> bindSlave lpat
  ConPat _ (L _ (GHC.Unqual occ)) (PrefixCon [] [lpat])
    | Just mk <- markerFromName occ -> FwdPat mk lpat
  -- empty list is done as the constructor
  ConPat _ (L _ rdr) _
    | rdr == thName '[] -> Vec loc []
    | rdr == thName '() -> Tuple []
  SigPat _ port ty -> PortType (hsps_body ty) (bindSlave port)
  LazyPat _ lpat -> Lazy loc (bindSlave lpat)
  ListPat _ pats -> Vec loc (map bindSlave pats)
  pat ->
    PortErr loc
            (mkLocMessage
              sevFatal
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
    | Just mk <- markerFromName occ -> FwdExpr mk sig
  ExplicitTuple _ tups _ -> let
    vals = fmap (\(Present _ e) -> e) tups
    in Tuple $ fmap bindMaster vals
  ExplicitList _ exprs ->
    Vec loc $ fmap bindMaster exprs
  -- XXX: Untested?
  HsProc _ _ (L _ (HsCmdTop _ (L _ (HsCmdArrApp _xapp (L _ (HsVar _ (L _ (GHC.Unqual occ)))) sig _ _))))
    | Just mk <- markerFromName occ -> FwdExpr mk sig
  ExprWithTySig _ expr' ty -> PortType (hsSigWcType ty) (bindMaster expr')

  HsParP expr' -> bindMaster expr'

  -- OpApp _xapp (L _ circuitVar) (L _ infixVar) appR -> k

  _ -> PortErr loc
    (mkLocMessage
      sevFatal
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
    OpApp _ circuit (L _ op) port | isFletching op -> do
      circuitBinds <>= [Binding
        { bCircuit = circuit
        , bOut     = bindMaster port
        , bIn      = fromMaybe (Tuple []) mInput
        }]

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

  duplicateMasters <- concat <$> forM (nonDetUniqMapToList nameMap) \(name, occ) -> do
    let isIgnored = case unpackFS name of {('_':_) -> True; _ -> False}

    case occ of
      ([], []) -> pure []
      ([_], [_]) -> pure []
      (s:_, []) | not isIgnored -> errM (locA s) ("Slave port " <> show name <> " has no associated master") >> pure []
      ([], m:_) | not isIgnored -> errM (locA m) ("Master port " <> show name <> " has no associated slave") >> pure []
      (ss@(s:_:_), _) ->
        -- would be nice to show locations of all occurrences here, not sure how to do that while
        -- keeping ghc api
        errM (locA s) ("Slave port " <> show name <> " defined " <> show (length ss) <> " times") >> pure []
      (_ss, ms) -> do
        -- if master is defined multiple times, we broadcast it
        if length ms > 1
          then pure [name]
          else pure []

  let
    modifyMulticast = \case
      Ref p@(PortName _ a) | a `elem` duplicateMasters -> RefMulticast p
      p -> p

  -- update relevant master ports to be multicast
  circuitSlaves %= L.transform modifyMulticast
  circuitMasters %= L.transform modifyMulticast
  circuitBinds . L.mapped %= \b -> b
    { bIn = L.transform modifyMulticast (bIn b),
      bOut = L.transform modifyMulticast (bOut b)
    }

-- Creating ------------------------------------------------------------

data Direction = Fwd | Bwd deriving Show

bindWithSuffix :: (p ~ GhcPs, ?nms :: ExternalNames) => GHC.DynFlags -> Direction -> PortDescription PortName -> LPat p
bindWithSuffix dflags dir = \case
  Tuple ps -> tildeP noSrcSpanA $ taggedBundleP $ tupP $ fmap (bindWithSuffix dflags dir) ps
  Vec s ps -> taggedBundleP $ vecP s $ fmap (bindWithSuffix dflags dir) ps
  Ref (PortName loc fs) -> varP loc (GHC.unpackFS fs <> "_" <> show dir)
  RefMulticast (PortName loc fs) -> case dir of
    Bwd -> L loc (WildPat noExtField)
    Fwd -> varP loc (GHC.unpackFS fs <> "_" <> show dir)
  PortErr loc msgdoc -> unsafePerformIO . throwOneError $
    mkLongErrMsg dflags (locA loc) Outputable.alwaysQualify (Outputable.text "Unhandled bind") msgdoc
  Lazy loc p -> tildeP loc $ bindWithSuffix dflags dir p
  -- XXX: propagate location
  FwdExpr _ (L _ _) -> nlWildPat
  FwdPat _ lpat -> tagP lpat
  SigTagExpr _ (L _ _) -> nlWildPat
  SigTagPat mk lpat -> sigTagP mk lpat
  PortType ty p -> tagTypeP dir ty $ bindWithSuffix dflags dir p

revDirec :: Direction -> Direction
revDirec = \case
  Fwd -> Bwd
  Bwd -> Fwd

bindOutputs
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => GHC.DynFlags
  -> Direction
  -> PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LPat p
bindOutputs dflags direc slaves masters = noLoc $ conPatIn (noLoc (fwdBwdCon ?nms)) (InfixCon m2s s2m)
  where
  m2s = bindWithSuffix dflags direc masters
  s2m = bindWithSuffix dflags (revDirec direc) slaves

expWithSuffix :: (p ~ GhcPs, ?nms :: ExternalNames) => Direction -> PortDescription PortName -> LHsExpr p
expWithSuffix dir = \case
  Tuple ps -> taggedBundleE $ tupE noSrcSpanA $ fmap (expWithSuffix dir) ps
  Vec s ps -> taggedBundleE $ vecE s $ fmap (expWithSuffix dir) ps
  Ref (PortName loc fs)   -> varE loc (var $ GHC.unpackFS fs <> "_" <> show dir)
  RefMulticast (PortName loc fs) -> case dir of
    Bwd -> varE noSrcSpanA (trivialBwd ?nms)
    Fwd -> varE loc (var $ GHC.unpackFS fs <> "_" <> show dir)
  -- laziness only affects the pattern side
  Lazy _ p   -> expWithSuffix dir p
  PortErr _ _ -> error "expWithSuffix PortErr!"
  FwdExpr _ lexpr -> tagE lexpr
  FwdPat _ (L l _) -> tagE $ varE l (trivialBwd ?nms)
  SigTagExpr mk lexpr -> sigTagE mk lexpr
  -- the backwards channel of a signal bus is trivial, so a plain (untyped)
  -- tag suffices; the forwards occurrence pins the bus type
  SigTagPat _ (L l _) -> tagE $ varE l (trivialBwd ?nms)
  PortType ty p -> tagTypeE dir ty (expWithSuffix dir p)

createInputs
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => Direction
  -> PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LHsExpr p
createInputs dir slaves masters = noLoc $ OpApp
#if __GLASGOW_HASKELL__ >= 912
  noExtField
#else
  noExt
#endif
  s2m (varE noSrcSpanA (fwdBwdCon ?nms)) m2s
  where
  m2s = expWithSuffix (revDirec dir) masters
  s2m = expWithSuffix dir slaves

decFromBinding :: (p ~ GhcPs, ?nms :: ExternalNames) => GHC.DynFlags -> Binding (LHsExpr p) PortName -> HsBind p
decFromBinding dflags Binding {..} = do
  let bindPat  = bindOutputs dflags Bwd bIn bOut
      inputExp = createInputs Fwd bOut bIn
      bod = runCircuitFun noSrcSpanA `appE` bCircuit `appE` inputExp
   in patBind bindPat bod

patBind :: LPat GhcPs -> LHsExpr GhcPs -> HsBind GhcPs
patBind lhs expr =
#if __GLASGOW_HASKELL__ < 910
  PatBind noExt lhs rhs
#else
  PatBind noExtField lhs (HsNoMultAnn noExtField) rhs
#endif
  where
    rhs :: GRHSs GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    rhs = GRHSs emptyComments [gr] $
      EmptyLocalBinds noExtField

    gr :: LGRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    gr =  L (noAnnSrcSpan (getLocA expr)) (GRHS noExt [] expr)

circuitConstructor :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsExpr GhcPs
circuitConstructor loc = varE loc (circuitCon ?nms)

runCircuitFun :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsExpr GhcPs
runCircuitFun loc = varE loc (runCircuitName ?nms)


prefixCon :: [arg] -> HsConDetails tyarg arg rec
prefixCon a = PrefixCon [] a

taggedBundleP :: (p ~ GhcPs, ?nms :: ExternalNames) => LPat p -> LPat p
taggedBundleP a = noLoc (conPatIn (noLoc (tagBundlePat ?nms)) (prefixCon [a]))

taggedBundleE :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsExpr p -> LHsExpr p
taggedBundleE a = varE noSrcSpanA (tagBundlePat ?nms) `appE` a

tagP :: (p ~ GhcPs, ?nms :: ExternalNames) => LPat p -> LPat p
tagP a = noLoc (conPatIn (noLoc (tagName ?nms)) (prefixCon [a]))

tagE :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsExpr p -> LHsExpr p
tagE a = varE noSrcSpanA (tagName ?nms) `appE` a

-- the SigTag wrappers take the location of what they wrap so that type
-- errors on the value boundary (e.g. marking a non-signal bus with @Signal@)
-- point at the marked pattern or expression
sigTagP :: (p ~ GhcPs, ?nms :: ExternalNames) => SigMarker -> LPat p -> LPat p
sigTagP mk a@(L l _) = L l (conPatIn (noLoc (markerTagName mk)) (prefixCon [a]))

sigTagE :: (p ~ GhcPs, ?nms :: ExternalNames) => SigMarker -> LHsExpr p -> LHsExpr p
sigTagE mk a@(L l _) = varE l (markerTagName mk) `appE` a

-- only value markers reach the SigTag* constructors, but keep this total
markerTagName :: (?nms :: ExternalNames) => SigMarker -> GHC.RdrName
markerTagName = \case
  SignalVMarker  -> signalTagName ?nms
  FwdVMarker     -> fwdTagName ?nms
  DSignalVMarker -> dSignalTagName ?nms
  SignalMarker   -> signalTagName ?nms
  FwdMarker      -> fwdTagName ?nms

tagTypeCon :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsType GhcPs
tagTypeCon =
    noLoc (HsTyVar noExt NotPromoted (noLoc (tagTName ?nms)))

sigPat :: (p ~ GhcPs) => SrcSpanAnnA -> LHsType GhcPs -> LPat p -> LPat p
sigPat loc ty a = L loc $
    SigPat noExt a (HsPS noExt ty)

sigE :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsType GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
sigE loc ty a = L loc $
    ExprWithTySig noExt a (HsWC noExtField (L loc $ HsSig noExtField (HsOuterImplicit noExtField) ty))

tagTypeP :: (p ~ GhcPs, ?nms :: ExternalNames) => Direction -> LHsType GhcPs -> LPat p -> LPat p
tagTypeP dir ty
  = sigPat noSrcSpanA (tagTypeCon `appTy` ty `appTy` busType)
  where
    busType = conT noSrcSpanA (fwdAndBwdTypes ?nms dir) `appTy` ty

tagTypeE :: (p ~ GhcPs, ?nms :: ExternalNames) => Direction -> LHsType GhcPs -> LHsExpr p -> LHsExpr p
tagTypeE dir ty a
  = sigE noSrcSpanA (tagTypeCon `appTy` ty `appTy` busType) a
  where
    busType = conT noSrcSpanA (fwdAndBwdTypes ?nms dir) `appTy` ty

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
#if __GLASGOW_HASKELL__ >= 910
    HsFunTy noExtField (HsUnrestrictedArrow noAnn)
#else
    HsFunTy noExt (HsUnrestrictedArrow $ L NoTokenLoc HsNormalTok)
#endif

arrTy :: p ~ GhcPs => LHsType p -> LHsType p -> LHsType p
arrTy a b = noLoc $ hsFunTy (parenthesizeHsType GHC.funPrec a) (parenthesizeHsType GHC.funPrec b)

varT :: SrcSpanAnnA -> String -> LHsType GhcPs
varT loc nm = L loc (HsTyVar noExt NotPromoted (noLoc (tyVar nm)))

conT :: SrcSpanAnnA -> GHC.RdrName -> LHsType GhcPs
conT loc nm = L loc (HsTyVar noExt NotPromoted (noLoc nm))

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
tyEq a b =
  noLoc $ HsOpTy
#if __GLASGOW_HASKELL__ >= 912
    noExtField
#else
    noExt
#endif
    NotPromoted a (noLoc eqTyCon_RDR) b
-- eqTyCon is a special name that has to be exactly correct for ghc to recognise it.

-- Final construction --------------------------------------------------

busCircuitQQExpM
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => CircuitM (LHsExpr p)
busCircuitQQExpM = do
  checkCircuit

  dflags <- GHC.getDynFlags
  binds <- L.use circuitBinds
  lets <- L.use circuitLets
  completes <- L.use circuitCompletes
  letTypes <- L.use circuitTypes
  slaves <- L.use circuitSlaves
  masters <- L.use circuitMasters

  -- Construction of the circuit expression.
  -- Locate each generated binding at its circuit expression so that type
  -- errors on a bus are reported on the offending statement rather than at
  -- the end of the circuit block (see tests/fixtures/BusError.hs).
  let decFromBinding' b@Binding{bCircuit = L cloc _} = L cloc (decFromBinding dflags b)
  let decs = lets <> completes <> map decFromBinding' binds

  let pats = bindOutputs dflags Fwd masters slaves
      res  = createInputs Bwd slaves masters

      body :: LHsExpr GhcPs
      body = letE noSrcSpanA letTypes decs res

  -- see [inference-helper]
  mapM_
    (\(Binding _ outs ins) -> gatherTypes outs >> gatherTypes ins)
    binds
  mapM_ gatherTypes [masters, slaves]

  pure $ circuitConstructor noSrcSpanA `appE` lamE [pats] body

-- Value-level ports (SignalV/FwdV markers) ----------------------------

-- | The number of value-level (@SignalV@/@FwdV@-marked) ports in a port
-- description.
countValuePorts :: PortDescription PortName -> Int
countValuePorts p =
  length [() | FwdPat mk _ <- L.universe p, isValueMarker mk] +
  length [() | FwdExpr mk _ <- L.universe p, isValueMarker mk]

-- | Replace each value-level ('Signal' / 'Fwd') pattern with a reference to a
-- generated signal bus variable (@prefix <> show i@), collecting the original
-- value-level patterns in order.
replaceFwdPats
  :: String
  -> PortDescription PortName
  -> State (Int, [(SigMarker, LPat GhcPs)]) (PortDescription PortName)
replaceFwdPats prefix = L.transformM \case
  FwdPat mk lpat@(L loc _) | isValueMarker mk -> do
    (i, pats) <- get
    put (i + 1, pats <> [(mk, lpat)])
    pure (SigTagPat mk (varP loc (prefix <> show i)))
  p -> pure p

-- | Replace each value-level ('Signal' / 'Fwd') expression with a reference
-- to a generated signal bus variable (@prefix <> show i@), collecting the
-- original value-level expressions in order.
replaceFwdExprs
  :: String
  -> PortDescription PortName
  -> State (Int, [(SigMarker, LHsExpr GhcPs)]) (PortDescription PortName)
replaceFwdExprs prefix = L.transformM \case
  FwdExpr mk lexpr@(L loc _) | isValueMarker mk -> do
    (i, exprs) <- get
    put (i + 1, exprs <> [(mk, lexpr)])
    pure (SigTagExpr mk (varE loc (var (prefix <> show i))))
  p -> pure p

-- | The value-aware entry point for @circuit@ blocks.
--
-- Value-level ports describe a circuit's logic over the values sampled
-- each clock cycle. The boundary between bus land and value land is marked
-- with @SignalV@ (or @FwdV@): @SignalV n <- ...@ binds @n@ to the per-cycle
-- value carried on that bus, and @... -< SignalV e@ injects the per-cycle
-- value @e@ back onto a bus.
--
-- All the value-level bindings (the @let@s of the do block) are collected
-- into a single pure function, @circuitLogic@, whose arguments are the
-- @Signal@-bound values and whose results are the @Signal@-injected
-- expressions. It is lifted to the signal level with 'fmap', using
-- 'bundle' / 'unbundle' and a lazy let binding to tie feedback loops:
--
-- @
-- circuitLogic = \\(ins) -> let \<user lets\> in (outs)
-- (outBuses) = unbundle (fmap circuitLogic (bundle (inBuses)))
-- @
--
-- The buses themselves are wired up exactly as for an ordinary @circuit@.
circuitQQExpM
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => CircuitM (LHsExpr p)
circuitQQExpM = do
  slaves0 <- L.use circuitSlaves
  masters0 <- L.use circuitMasters
  binds0 <- L.use circuitBinds

  let boundaryCount =
        sum (map countValuePorts (slaves0 : masters0 : concatMap (\b -> [bIn b, bOut b]) binds0))

  -- Without any value-level (SignalV/FwdV) ports there is no boundary to
  -- lift; generate plain bus plumbing.
  if boundaryCount == 0 then busCircuitQQExpM else valueCircuitQQExpM

valueCircuitQQExpM
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => CircuitM (LHsExpr p)
valueCircuitQQExpM = do
  checkCircuit

  dflags <- GHC.getDynFlags
  loc <- L.use circuitLoc

  -- read the ports after checkCircuit, which may have rewritten them
  slaves0 <- L.use circuitSlaves
  masters0 <- L.use circuitMasters
  binds0 <- L.use circuitBinds

  let inPrefix  = genLocName loc "valIn" <> "_"
      outPrefix = genLocName loc "valOut" <> "_"
      logicName = genLocName loc "circuitLogic"

  -- Value patterns become the arguments of circuitLogic (values sampled off
  -- buses) ...
  let inM = do
        s <- replaceFwdPats inPrefix slaves0
        bs <- traverse (\b -> (\p -> b { bIn = p }) <$> replaceFwdPats inPrefix (bIn b)) binds0
        pure (s, bs)
      ((slaves1, binds1), (numIns, inPats)) = runState inM (0, [])

  -- ... and value expressions become its results (values written to buses).
  let outM = do
        bs <- traverse (\b -> (\p -> b { bOut = p }) <$> replaceFwdExprs outPrefix (bOut b)) binds1
        m <- replaceFwdExprs outPrefix masters0
        pure (bs, m)
      ((binds2, masters1), (numOuts, outExprs)) = runState outM (0, [])

  circuitSlaves .= slaves1
  circuitMasters .= masters1
  circuitBinds .= binds2

  -- In a value circuit the do-block lets are value-level; they form the
  -- bodies of the generated logic functions rather than ending up in the
  -- outer (bus-level) let -- except for lets that don't touch any
  -- value-level variable, which stay in the outer let (so e.g. a let-bound
  -- sub-circuit can still be used with @-<@).
  lets <- L.use circuitLets
  completes <- L.use circuitCompletes
  letTypes <- L.use circuitTypes

  -- see [value-components]
  let valueNames = Set.fromList (concatMap (patVarNames . snd) inPats <> concatMap bindDefinedNames lets)
      valueFvs :: SYB.Data a => a -> Set.Set String
      valueFvs a = Set.intersection (freeVarNames a) valueNames

      items =
        [ (ItemIn i, Set.fromList (patVarNames p)) | (i, (_, p)) <- zip [0 ..] inPats ] <>
        [ (ItemOut k, valueFvs e) | (k, (_, e)) <- zip [0 ..] outExprs ] <>
        [ (ItemLet j, Set.fromList (bindDefinedNames b) `Set.union` valueFvs b)
        | (j, b) <- zip [0 ..] lets ]

      itemSeq = \case
        ItemIn i  -> i
        ItemOut k -> numIns + k
        ItemLet j -> numIns + numOuts + j
      isBoundary = \case ItemLet{} -> False; _ -> True

      groups = sortOn (minimum . map itemSeq . fst) (groupComponents items)
      (innerGroups, outerGroups) = partition (any isBoundary . fst) groups

      -- lets disconnected from the value boundary stay in the outer let
      outerLets = [ lets !! j | (its, _) <- outerGroups, ItemLet j <- its ]

      -- assign user type signatures to the group that binds their name,
      -- splitting multi-name signatures if necessary
      nameComp = Map.fromList
        [ (n, ci) | (ci, (_, ns)) <- zip [0 :: Int ..] innerGroups, n <- Set.toList ns ]
      sigComp (L _ rdr) = case unqualName rdr of
        [n] -> Map.lookup n nameComp
        _   -> Nothing
      splitSigs = concatMap
        (\lsig@(L l s) -> case s of
            TypeSig x ids ty ->
              [ (c, L l (TypeSig x ids' ty))
              | (c, ids') <- Map.toList (Map.fromListWith (flip (<>)) [ (sigComp i, [i]) | i <- ids ]) ]
            _ -> [(Nothing, lsig)])
        letTypes
      sigsForComp ci = [ s | (Just ci', s) <- splitSigs, ci' == ci ]
      outerSigs = [ s | (Nothing, s) <- splitSigs ]

  -- Each group is lifted with the bundle matching its markers' flavor;
  -- plain (SignalV/FwdV) and delayed (DSignalV) values cannot meet in one
  -- group, since neither bundle accepts both bus kinds.
  flavors <- forM innerGroups \(its, _) -> do
    let mks = [ (fst (inPats !! i), getLoc (snd (inPats !! i))) | ItemIn i <- its ]
           <> [ (fst (outExprs !! k), getLoc (snd (outExprs !! k))) | ItemOut k <- its ]
        dLocs = [ l | (mk, l) <- mks, valueMarkerFlavor mk == DSignalGroup ]
        sLocs = [ l | (mk, l) <- mks, valueMarkerFlavor mk == SignalGroup ]
    case (dLocs, sLocs) of
      (dl : _, _ : _) -> do
        errM (locA dl) $
          "This value group mixes DSignalV with SignalV/FwdV markers. "
          <> "Delayed and undelayed values cannot meet in one logic group; "
          <> "convert between Signal and DSignal explicitly at the bus level "
          <> "instead."
        pure DSignalGroup
      (_ : _, []) -> pure DSignalGroup
      _           -> pure SignalGroup

      -- One logic function and one lifted knot binding per group:
      --   circuitLogic_cN = \(ins) -> let <lets> in (outs)
      --   (outBuses) = unbundle (fmap circuitLogic_cN (bundle (inBuses)))
      -- bundle/unbundle are only needed when there is more than one bus, and
      -- with no inputs at all the logic is constant, so it is mapped over
      -- @pure ()@. The generated bundle elements and knot patterns take the
      -- source locations of the original markers, so clock domain (and
      -- delay) mismatches are reported on the offending marker. Groups with
      -- no outputs produce no value (their logic would be dead) and generate
      -- nothing.
  let mkComp ci flavor (its, _) =
        let ins  = sort [ i | ItemIn i <- its ]
            outs = sort [ k | ItemOut k <- its ]
            ls   = sort [ j | ItemLet j <- its ]
            (bundleNm, unbundleNm) = case flavor of
              SignalGroup  -> (thName 'bundle, thName 'unbundle)
              DSignalGroup -> (thName 'DBundle.bundle, thName 'DBundle.unbundle)
            logicNm = logicName <> "_c" <> show ci
            logicLam = lamE [tupP (map (snd . (inPats !!)) ins)]
              (letE noSrcSpanA (sigsForComp ci) (map (lets !!) ls)
                    (tupE noSrcSpanA (map (snd . (outExprs !!)) outs)))
            logicBind = L loc $ patBind (varP noSrcSpanA logicNm) logicLam

            inVars = map (\i -> let (L l _) = snd (inPats !! i) in varE l (var (inPrefix <> show i))) ins
            outVarPs = map (\k -> let (L l _) = snd (outExprs !! k) in varP l (outPrefix <> show k)) outs

            bundled = case inVars of
              []  -> varE noSrcSpanA (thName 'pure) `appE` tupE noSrcSpanA []
              [e] -> e
              es  -> varE noSrcSpanA bundleNm `appE` tupE noSrcSpanA es
            lifted = varE noSrcSpanA (thName 'fmap) `appE` varE noSrcSpanA (var logicNm) `appE` bundled
            knotExpr = if length outs > 1
              then varE noSrcSpanA unbundleNm `appE` lifted
              else lifted
            knotBind = L loc $ patBind (tupP outVarPs) knotExpr
        in if null outs then [] else [logicBind, knotBind]

      compDecs = concat (zipWith3 mkComp [0 ..] flavors innerGroups)

  -- The bus plumbing is generated exactly as in 'busCircuitQQExpM'.
  let decFromBinding' b@Binding{bCircuit = L cloc _} = L cloc (decFromBinding dflags b)
  let decs = compDecs <> outerLets <> completes <> map decFromBinding' binds2

  let pats = bindOutputs dflags Fwd masters1 slaves1
      res  = createInputs Bwd slaves1 masters1

      body :: LHsExpr GhcPs
      body = letE noSrcSpanA outerSigs decs res

  pure $ circuitConstructor noSrcSpanA `appE` lamE [pats] body

-- [value-components]
-- The value-level bindings of a @circuit@ block are split into the
-- connected components of their shared-variable graph before lifting: an
-- input variable (Signal pattern), output expression (Signal expression) or
-- let binding belongs to the same group as anything it shares a value-level
-- variable with. Each group is lifted with its own fmap/bundle/unbundle, so
-- only buses whose values actually meet are bundled -- which is what allows
-- a single circuit block to span several clock domains: per-cycle values
-- may only meet if their buses are synchronous, and 'bundle' enforces
-- exactly that per group. Sharing a variable across domains is an
-- (unsynchronized) clock domain crossing and is rejected by the type
-- checker; crossing domains must be done with explicit bus-level
-- synchronizer circuits.
--
-- The analysis is purely syntactic and conservative: free variables are
-- over-approximated by all unqualified variable occurrences (no scope
-- tracking), so shadowing can only ever merge groups that strictly wouldn't
-- need merging (a false same-domain constraint), never split things that
-- belong together.

-- | An occurrence of the value boundary (or a let between boundaries) in a
-- @circuit@ block; the @Int@ indexes into the respective collection.
data ValueItem = ItemIn Int | ItemOut Int | ItemLet Int

-- | Group items into connected components: items (transitively) sharing a
-- name end up in the same group.
groupComponents :: [(ValueItem, Set.Set String)] -> [([ValueItem], Set.Set String)]
groupComponents = foldl step []
  where
    step groups (it, ns) =
      let (touching, rest) = partition (\(_, gns) -> not (Set.disjoint ns gns)) groups
      in (concatMap fst touching <> [it], Set.unions (ns : map snd touching)) : rest

unqualName :: GHC.RdrName -> [String]
unqualName = \case
  GHC.Unqual occ -> [OccName.occNameString occ]
  _ -> []

-- | Variable names bound by a pattern (conservative, syntactic; as-pattern
-- names are not collected).
patVarNames :: LPat GhcPs -> [String]
patVarNames = SYB.everything (<>) (SYB.mkQ [] q)
  where
    q :: Pat GhcPs -> [String]
    q = \case
      VarPat _ (L _ rdr) -> unqualName rdr
      _ -> []

-- | All unqualified variable occurrences: a conservative over-approximation
-- of the free variables (bound variables of nested lambdas/lets/cases are
-- included).
freeVarNames :: SYB.Data a => a -> Set.Set String
freeVarNames = Set.fromList . SYB.everything (<>) (SYB.mkQ [] q)
  where
    q :: HsExpr GhcPs -> [String]
    q = \case
      HsVar _ (L _ rdr) -> unqualName rdr
      _ -> []

-- | The names a let binding defines.
bindDefinedNames :: LHsBind GhcPs -> [String]
bindDefinedNames (L _ b) = case b of
  FunBind { fun_id = L _ rdr } -> unqualName rdr
  PatBind { pat_lhs = lpat } -> patVarNames lpat
  VarBind { var_id = rdr } -> unqualName rdr
  _ -> []

grr :: MonadIO m => OccName.NameSpace -> m ()
grr nm
  | nm == OccName.tcName = liftIO $ putStrLn "tcName"
  | nm == OccName.clsName = liftIO $ putStrLn "clsName"
  | nm == OccName.tcClsName = liftIO $ putStrLn "tcClsName"
  | nm == OccName.dataName = liftIO $ putStrLn "dataName"
  | nm == OccName.varName = liftIO $ putStrLn "varName"
  | nm == OccName.tvName = liftIO $ putStrLn "tvName"
  | otherwise = liftIO $ putStrLn "I dunno"

completeUnderscores :: (?nms :: ExternalNames) => CircuitM ()
completeUnderscores = do
  binds <- L.use circuitBinds
  masters <- L.use circuitMasters
  slaves <- L.use circuitSlaves
  let addDef :: String -> PortDescription PortName -> CircuitM ()
      addDef suffix = \case
        Ref (PortName loc (unpackFS -> name@('_':_))) -> do
          let bind = patBind (varP loc (name <> suffix)) (tagE $ varE loc (thName 'def))
          circuitCompletes <>= [L loc bind]

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
    -> GHC.Located (HsModule GhcPs)
    -> GHC.Hsc (GHC.Located (HsModule GhcPs))
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
    | isDollar infixVar && dollarChainIsCircuit "circuit" circuitVar = do
        runCircuitM $ do
          x <- parseCircuit appR >> completeUnderscores >> circuitQQExpM
          when debug $ ppr x
          pure (dollarChainReplaceCircuit "circuit" x c)

  transform' e = pure e

-- | check if the named circuit keyword is applied via `a $ chain $ of $ dollars`.
dollarChainIsCircuit :: GHC.FastString -> HsExpr GhcPs -> Bool
dollarChainIsCircuit nm = \case
  HsVar _ (L _ v)                             -> v == GHC.mkVarUnqual nm
  OpApp _xapp _appL (L _ infixVar) (L _ appR) -> isDollar infixVar && dollarChainIsCircuit nm appR
  _                                           -> False

-- | Replace the circuit if it's part of a chain of `$`.
dollarChainReplaceCircuit :: GHC.FastString -> LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
dollarChainReplaceCircuit nm circuitExpr (L loc app) = case app of
  HsVar _ (L _loc v)
    -> if v == GHC.mkVarUnqual nm
         then circuitExpr
         else error "dollarChainAddCircuit: not a circuit"
  OpApp xapp appL (L infixLoc infixVar) appR
    -> L loc $ OpApp xapp appL (L infixLoc infixVar) (dollarChainReplaceCircuit nm circuitExpr appR)
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
  logger <- GHC.getLogger
  let
    diagOpts = GHC.initDiagOpts dflags
    mc = Err.mkMCDiagnostic diagOpts GHC.WarningWithoutFlag
           Nothing
  liftIO $ GHC.logMsg logger mc noSrcSpan sdoc

-- | The actual implementation.
pluginImpl ::
  (?nms :: ExternalNames) => [GHC.CommandLineOption] -> GHC.ModSummary ->
  GHC.ParsedResult -> GHC.Hsc GHC.ParsedResult
pluginImpl cliOptions _modSummary m = do
    -- cli options are activated by -fplugin-opt=CircuitNotation:debug
    debug <- case cliOptions of
      []        -> pure False
      ["debug"] -> pure True
      _ -> do
        warningMsg $ Outputable.text $ "CircuitNotation: unknown cli options " <> show cliOptions
        pure False
    hpm_module' <- do
      transform debug $ GHC.hpm_module $ GHC.parsedResultModule m
    let parsedResultModule' = (GHC.parsedResultModule m)
                                { GHC.hpm_module = hpm_module' }
        module' = m { GHC.parsedResultModule = parsedResultModule' }
    return module'

-- Debugging functions -------------------------------------------------

ppr :: GHC.Outputable a => a -> CircuitM ()
ppr a = do
  dflags <- GHC.getDynFlags
  liftIO $ putStrLn (GHC.showPpr dflags a)

showC :: Data.Data a => a -> String
showC a = show (typeOf a) <> " " <> show (Data.toConstr a)

-- Names ---------------------------------------------------------------

-- | Recognise the port marker keywords (see 'SigMarker').
markerFromName :: OccName.OccName -> Maybe SigMarker
markerFromName occ = case OccName.occNameString occ of
  "Signal"   -> Just SignalMarker
  "Fwd"      -> Just FwdMarker
  "SignalV"  -> Just SignalVMarker
  "FwdV"     -> Just FwdVMarker
  "DSignalV" -> Just DSignalVMarker
  _          -> Nothing

-- | Collection of names external to circuit-notation.
data ExternalNames = ExternalNames
  { circuitCon :: GHC.RdrName
  , runCircuitName :: GHC.RdrName
  , tagBundlePat :: GHC.RdrName
  , tagName :: GHC.RdrName
  , signalTagName :: GHC.RdrName
  -- ^ a (pattern synonym) variant of 'tagName' whose type pins the bus to be
  -- a signal; used for @Signal@ markers at the value boundary of @circuitV@
  -- blocks
  , fwdTagName :: GHC.RdrName
  -- ^ like 'signalTagName' but class-constrained, accepting any signal-like
  -- bus; used for @FwdV@ markers at the value boundary of @circuit@ blocks
  , dSignalTagName :: GHC.RdrName
  -- ^ like 'signalTagName' for delayed signals; used for @DSignalV@ markers
  , tagTName :: GHC.RdrName
  , fwdBwdCon :: GHC.RdrName
  , fwdAndBwdTypes :: Direction -> GHC.RdrName
  , trivialBwd :: GHC.RdrName
  , consPat :: GHC.RdrName
  }

-- | The names used by the plugin by default, referring to the @Circuit@
-- module of this package. Custom plugins are encouraged to build their
-- names as a record update of this, so that newly added fields (which
-- happens when the notation grows new features) default to something
-- sensible.
defExternalNames :: ExternalNames
defExternalNames = ExternalNames
  { circuitCon = GHC.Unqual (OccName.mkDataOcc "TagCircuit")
  , runCircuitName = GHC.Unqual (OccName.mkVarOcc "runTagCircuit")
  , tagBundlePat = GHC.Unqual (OccName.mkDataOcc "BusTagBundle")
  , tagName = GHC.Unqual (OccName.mkDataOcc "BusTag")
  , signalTagName = GHC.Unqual (OccName.mkDataOcc "SigTag")
  , fwdTagName = GHC.Unqual (OccName.mkDataOcc "FwdTag")
  , dSignalTagName = GHC.Unqual (OccName.mkDataOcc "DSigTag")
  , tagTName = GHC.Unqual (OccName.mkTcOcc "BusTag")
  , fwdBwdCon = GHC.Unqual (OccName.mkDataOcc ":->")
  , fwdAndBwdTypes = \case
      Fwd -> GHC.Unqual (OccName.mkTcOcc "Fwd")
      Bwd -> GHC.Unqual (OccName.mkTcOcc "Bwd")
  , trivialBwd = GHC.Unqual (OccName.mkVarOcc "unitBwd")
  , consPat = GHC.Unqual (OccName.mkDataOcc ":>!")
  }
