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

-- TODO: Fix warnings introduced by GHC 9.2
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CircuitNotation
  ( plugin
  , mkPlugin
  , thName
  , ExternalNames (..)
  , Direction(..)
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

#if __GLASGOW_HASKELL__ >= 910
import           GHC.Hs (EpAnn)
#endif

#if __GLASGOW_HASKELL__ >= 900
import           GHC.Data.Bag
import           GHC.Data.FastString       (mkFastString, unpackFS)
#if __GLASGOW_HASKELL__ < 906
import           GHC.Plugins               (PromotionFlag(NotPromoted))
#endif
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

#if __GLASGOW_HASKELL__ >= 904
import GHC.Driver.Errors.Ppr () -- instance Diagnostic GhcMessage

import qualified GHC.Driver.Config.Diagnostic as GHC
import qualified GHC.Driver.Errors.Types      as GHC
import qualified GHC.Utils.Logger             as GHC
import qualified GHC.Parser.PostProcess       as GHC
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

#if __GLASGOW_HASKELL__ < 908
import GHC.Types.Unique.Map.Extra
#endif

-- clash-prelude
import Clash.Prelude (Vec((:>), Nil))

-- lens
import qualified Control.Lens           as L
import           Control.Lens.Operators

-- mtl
import           Control.Monad.State

#if __GLASGOW_HASKELL__ >= 906
import           Control.Monad
#endif

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
#if __GLASGOW_HASKELL__ < 902
type MsgDoc = Err.MsgDoc
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
#elif __GLASGOW_HASKELL__ < 910
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

#if __GLASGOW_HASKELL__ < 902
type ErrMsg = Err.ErrMsg
#elif __GLASGOW_HASKELL__ >= 902 && __GLASGOW_HASKELL__ < 904
type ErrMsg = Err.MsgEnvelope Err.DecoratedSDoc
#else
type ErrMsg = Err.MsgEnvelope GHC.GhcMessage
#endif

#if __GLASGOW_HASKELL__ < 904
sevFatal :: Err.Severity
sevFatal = Err.SevFatal
#else
sevFatal :: Err.MessageClass
sevFatal = Err.MCFatal
#endif

#if __GLASGOW_HASKELL__ >= 910
noExt :: NoAnn a => a
noExt = noAnn

instance NoAnn NoExtField where
  noAnn = noExtField
#elif __GLASGOW_HASKELL__ > 900
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

#if __GLASGOW_HASKELL__ < 904
pattern HsParP :: LHsExpr p -> HsExpr p
pattern HsParP e <- HsPar _ e

pattern ParPatP :: LPat p -> Pat p
pattern ParPatP p <- ParPat _ p
#elif __GLASGOW_HASKELL__ < 910
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

#if __GLASGOW_HASKELL__ < 906
type PrintUnqualified = Outputable.PrintUnqualified
#else
type PrintUnqualified = Outputable.NamePprCtx
#endif

mkErrMsg :: GHC.DynFlags -> SrcSpan -> PrintUnqualified -> Outputable.SDoc -> ErrMsg
#if __GLASGOW_HASKELL__ < 902
mkErrMsg = Err.mkErrMsg
#elif __GLASGOW_HASKELL__ >= 902 && __GLASGOW_HASKELL__ < 904
mkErrMsg _ = Err.mkMsgEnvelope
#else
-- Check the documentation of
-- `GHC.Driver.Errors.Types.ghcUnkownMessage` for some background on
-- why plugins should use this generic message constructor.
mkErrMsg _ locn unqual =
    Err.mkErrorMsgEnvelope locn unqual
  . GHC.ghcUnknownMessage
  . Err.mkPlainError Err.noHints
#endif

mkLongErrMsg :: GHC.DynFlags -> SrcSpan -> PrintUnqualified -> Outputable.SDoc -> Outputable.SDoc -> ErrMsg
#if __GLASGOW_HASKELL__ < 902
mkLongErrMsg = Err.mkLongErrMsg
#elif __GLASGOW_HASKELL__ >= 902 && __GLASGOW_HASKELL__ < 904
mkLongErrMsg _ = Err.mkLongMsgEnvelope
#else
mkLongErrMsg _ locn unqual msg extra =
    Err.mkErrorMsgEnvelope locn unqual
  $ GHC.ghcUnknownMessage
  $ Err.mkDecoratedError Err.noHints [msg, extra]
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
    | RefMulticast a
    | Lazy SrcSpanAnnA (PortDescription a)
    | FwdExpr (LHsExpr GhcPs)
    | FwdPat (LPat GhcPs)
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
#if __GLASGOW_HASKELL__ < 904
  unless (isEmptyBag errs) $ liftIO . throwIO $ GHC.mkSrcErr errs
#else
  unless (isEmptyBag errs) $ liftIO . throwIO $ GHC.mkSrcErr $ Err.mkMessages errs
#endif
  pure a

#if __GLASGOW_HASKELL__ < 904
mkLocMessage :: Err.Severity -> SrcSpan -> Outputable.SDoc -> Outputable.SDoc
#else
mkLocMessage :: Err.MessageClass -> SrcSpan -> Outputable.SDoc -> Outputable.SDoc
#endif

#if __GLASGOW_HASKELL__ < 906
mkLocMessage = Err.mkLocMessageAnn Nothing
#else
mkLocMessage = Err.mkLocMessage
#endif

errM :: SrcSpan -> String -> CircuitM ()
errM loc msg = do
  dflags <- GHC.getDynFlags
  let errMsg = mkLocMessage sevFatal loc (Outputable.text msg)
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

#if __GLASGOW_HASKELL__ >= 910
noEpAnn :: NoAnn ann => GenLocated SrcSpan e -> GenLocated (EpAnn ann) e
noEpAnn (L l e) = L (EpAnn (spanAsAnchor l) noAnn emptyComments) e

noLoc :: NoAnn ann => e -> GenLocated (EpAnn ann) e
noLoc = noEpAnn . GHC.noLoc
#elif __GLASGOW_HASKELL__ >= 902
noEpAnn :: GenLocated SrcSpan e -> GenLocated (SrcAnn ann) e
noEpAnn (L l e) = L (SrcSpanAnn noExt l) e

noLoc :: e -> GenLocated (SrcAnn ann) e
noLoc = noEpAnn . GHC.noLoc
#else
noLoc :: e -> Located e
noLoc = GHC.noLoc
#endif

tupP :: p ~ GhcPs => [LPat p] -> LPat p
tupP [pat] = pat
tupP pats = noLoc $ TuplePat noExt pats GHC.Boxed

vecP :: (?nms :: ExternalNames) => SrcSpanAnnA -> [LPat GhcPs] -> LPat GhcPs
vecP srcLoc = \case
  [] -> go []
#if __GLASGOW_HASKELL__ < 904
  as -> L srcLoc $ ParPat noExt $ go as
  where
#elif __GLASGOW_HASKELL__ < 910
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
    let
#if __GLASGOW_HASKELL__ >= 902
      l1 = l0 `seq` noSrcSpanA
#else
      l1 = l0
#endif
    in
      L srcLoc $ conPatIn (L l1 (consPat ?nms)) (InfixCon p (go pats))
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
vecT s tys@(ty:_) = L s $ HsParTy noExt (conT s (thName ''Vec) `appTy` tyNum s (length tys) `appTy` ty)

tyNum :: SrcSpanAnnA -> Int -> LHsType GhcPs
tyNum s i = L s (HsTyLit noExtField (HsNumTy GHC.NoSourceText (fromIntegral i)))

appTy :: LHsType GhcPs -> LHsType GhcPs -> LHsType GhcPs
appTy a b = noLoc (HsAppTy noExtField a (parenthesizeHsType GHC.appPrec b))

appE :: LHsExpr GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
appE fun arg = L noSrcSpanA $ HsApp noExt fun (parenthesizeHsExpr GHC.appPrec arg)

varE :: SrcSpanAnnA -> GHC.RdrName -> LHsExpr GhcPs
varE loc rdr = L loc (HsVar noExtField (noLoc rdr))

parenE :: LHsExpr GhcPs -> LHsExpr GhcPs
#if __GLASGOW_HASKELL__ < 904
parenE e@(L l _) = L l (HsPar noExt e)
#elif __GLASGOW_HASKELL__ < 910
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
#if __GLASGOW_HASKELL__ < 906
  HsLam _ (MG _x alts _origin) <- Just expr
#elif __GLASGOW_HASKELL__ < 910
  HsLam _ (MG _x alts) <- Just expr
#else
  HsLam _ _ (MG _x alts) <- Just expr
#endif
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
letE loc sigs binds expr =
#if __GLASGOW_HASKELL__ < 904
    L loc (HsLet noExt localBinds expr)
#elif __GLASGOW_HASKELL__ < 908
    L loc (HsLet noExt tkLet localBinds tkIn expr)
#elif __GLASGOW_HASKELL__ < 910
    L loc (HsLet noExt tkLet localBinds tkIn expr)
#else
    L loc (HsLet (tkLet,tkIn) localBinds expr)
#endif
  where
#if __GLASGOW_HASKELL__ >= 902
    localBinds :: HsLocalBinds GhcPs
    localBinds = HsValBinds noExt valBinds
#else
    localBinds :: LHsLocalBindsLR GhcPs GhcPs
    localBinds = L loc $ HsValBinds noExt valBinds
#endif

#if __GLASGOW_HASKELL__ >= 910
    tkLet = EpTok $ spanAsAnchor $ locA loc
    tkIn  = EpTok $ spanAsAnchor $ locA loc
#elif __GLASGOW_HASKELL__ >= 904
    tkLet = L (GHC.mkTokenLocation $ locA loc) HsTok
    tkIn  = L (GHC.mkTokenLocation $ locA loc) HsTok
#endif

    valBinds :: HsValBindsLR GhcPs GhcPs
    valBinds = ValBinds noAnnSortKey hsBinds sigs

    hsBinds :: LHsBindsLR GhcPs GhcPs
    hsBinds = listToBag binds

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
#if __GLASGOW_HASKELL__ < 906
    mg = MG noExtField matches GHC.Generated
#elif __GLASGOW_HASKELL__ < 908
    mg = MG GHC.Generated matches
#elif __GLASGOW_HASKELL__ < 910
    mg = MG (GHC.Generated GHC.DoPmc) matches
#else
    mg = MG (GHC.Generated GHC.OtherExpansion GHC.DoPmc) matches
#endif

    matches :: GenLocated SrcSpanAnnL [GenLocated SrcSpanAnnA (Match GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))]
    matches = noLoc $ [singleMatch]

    singleMatch :: GenLocated SrcSpanAnnA (Match GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
#if __GLASGOW_HASKELL__ >= 910
    singleMatch = noLoc $ Match noExt (LamAlt LamSingle) pats grHss
#else
    singleMatch = noLoc $ Match noExt LambdaExpr pats grHss
#endif

    grHss :: GRHSs GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    grHss = GRHSs emptyComments [grHs] $
#if __GLASGOW_HASKELL__ >= 902
      (EmptyLocalBinds noExtField)
#else
      (noLoc (EmptyLocalBinds noExtField))
#endif

#if __GLASGOW_HASKELL__ < 904
    grHs :: GenLocated SrcSpan (GRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
    grHs = L noSrcSpan $ GRHS noExt [] expr
#else
    grHs :: LGRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    grHs =  L noSrcSpanA $ GRHS noExt [] expr
#endif

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
  ParPatP lpat -> bindSlave lpat
#if __GLASGOW_HASKELL__ >= 902
  ConPat _ (L _ (GHC.Unqual occ)) (PrefixCon [] [lpat])
#elif __GLASGOW_HASKELL__ >= 900
  ConPat _ (L _ (GHC.Unqual occ)) (PrefixCon [lpat])
#else
  ConPatIn (L _ (GHC.Unqual occ)) (PrefixCon [lpat])
#endif
    | OccName.occNameString occ `elem` fwdNames -> FwdPat lpat
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
    | OccName.occNameString occ `elem` fwdNames -> FwdExpr sig
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
    | OccName.occNameString occ `elem` fwdNames -> FwdExpr sig
  ExprWithTySig ty expr' -> PortType (hsSigWcType ty) (bindMaster expr')
  ELazyPat _ expr' -> Lazy loc (bindMaster expr')
#else
  -- XXX: Untested?
  HsProc _ _ (L _ (HsCmdTop _ (L _ (HsCmdArrApp _xapp (L _ (HsVar _ (L _ (GHC.Unqual occ)))) sig _ _))))
    | OccName.occNameString occ `elem` fwdNames -> FwdExpr sig
  ExprWithTySig _ expr' ty -> PortType (hsSigWcType ty) (bindMaster expr')
#endif

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
#if __GLASGOW_HASKELL__ >= 902
  -- XXX: propagate location
  FwdExpr (L _ _) -> nlWildPat
#else
  FwdExpr (L l _) -> L l (WildPat noExt)
#endif
  FwdPat lpat -> tagP lpat
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
  FwdExpr lexpr -> tagE lexpr
  FwdPat (L l _) -> tagE $ varE l (trivialBwd ?nms)
  PortType ty p -> tagTypeE dir ty (expWithSuffix dir p)

createInputs
  :: (p ~ GhcPs, ?nms :: ExternalNames)
  => Direction
  -> PortDescription PortName
  -- ^ slave ports
  -> PortDescription PortName
  -- ^ master ports
  -> LHsExpr p
createInputs dir slaves masters = noLoc $ OpApp noExt s2m (varE noSrcSpanA (fwdBwdCon ?nms)) m2s
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
#if __GLASGOW_HASKELL__ < 906
  PatBind noExt lhs rhs ([], [])
#elif __GLASGOW_HASKELL__ < 910
  PatBind noExt lhs rhs
#else
  PatBind noExt lhs (HsNoMultAnn noExt) rhs
#endif
  where
    rhs :: GRHSs GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    rhs = GRHSs emptyComments [gr] $
#if __GLASGOW_HASKELL__ >= 902
      EmptyLocalBinds noExtField
#else
      noLoc (EmptyLocalBinds noExtField)
#endif

#if __GLASGOW_HASKELL__ < 904
    gr :: GenLocated SrcSpan (GRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs)))
    gr  = L (locA (getLoc expr)) (GRHS noExt [] expr)
#else
    gr :: LGRHS GhcPs (GenLocated SrcSpanAnnA (HsExpr GhcPs))
    gr =  L (noAnnSrcSpan (getLocA expr)) (GRHS noExt [] expr)
#endif

circuitConstructor :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsExpr GhcPs
circuitConstructor loc = varE loc (circuitCon ?nms)

runCircuitFun :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsExpr GhcPs
runCircuitFun loc = varE loc (runCircuitName ?nms)


#if __GLASGOW_HASKELL__ < 902
prefixCon :: [arg] -> HsConDetails arg rec
prefixCon a = PrefixCon a
#else
prefixCon :: [arg] -> HsConDetails tyarg arg rec
prefixCon a = PrefixCon [] a
#endif

taggedBundleP :: (p ~ GhcPs, ?nms :: ExternalNames) => LPat p -> LPat p
taggedBundleP a = noLoc (conPatIn (noLoc (tagBundlePat ?nms)) (prefixCon [a]))

taggedBundleE :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsExpr p -> LHsExpr p
taggedBundleE a = varE noSrcSpanA (tagBundlePat ?nms) `appE` a

tagP :: (p ~ GhcPs, ?nms :: ExternalNames) => LPat p -> LPat p
tagP a = noLoc (conPatIn (noLoc (tagName ?nms)) (prefixCon [a]))

tagE :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsExpr p -> LHsExpr p
tagE a = varE noSrcSpanA (tagName ?nms) `appE` a

tagTypeCon :: (p ~ GhcPs, ?nms :: ExternalNames) => LHsType GhcPs
tagTypeCon =
    noLoc (HsTyVar noExt NotPromoted (noLoc (tagTName ?nms)))

sigPat :: (p ~ GhcPs) => SrcSpanAnnA -> LHsType GhcPs -> LPat p -> LPat p
sigPat loc ty a = L loc $
#if __GLASGOW_HASKELL__ < 810
    SigPat (HsWC noExt (HsIB noExt ty)) a
#elif __GLASGOW_HASKELL__ < 900
    SigPat noExt a (HsWC noExt (HsIB noExt ty))
#else
    SigPat noExt a (HsPS noExt ty)
#endif

sigE :: (?nms :: ExternalNames) => SrcSpanAnnA -> LHsType GhcPs -> LHsExpr GhcPs -> LHsExpr GhcPs
sigE loc ty a = L loc $
#if __GLASGOW_HASKELL__ < 810
    ExprWithTySig (HsWC noExt (HsIB noExt ty)) a
#elif __GLASGOW_HASKELL__ < 902
    ExprWithTySig noExt a (HsWC noExt (HsIB noExt ty))
#else
    ExprWithTySig noExt a (HsWC noExtField (L loc $ HsSig noExtField (HsOuterImplicit noExtField) ty))
#endif

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
    HsFunTy noExt (HsUnrestrictedArrow noExt)
#elif __GLASGOW_HASKELL__ >= 904
    HsFunTy noExt (HsUnrestrictedArrow $ L NoTokenLoc HsNormalTok)
#elif __GLASGOW_HASKELL__ >= 900
    HsFunTy noExt (HsUnrestrictedArrow GHC.NormalSyntax)
#else
    HsFunTy noExt
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
#if __GLASGOW_HASKELL__ < 904
  noLoc $ HsOpTy noExtField a (noLoc eqTyCon_RDR) b
#else
  noLoc $ HsOpTy noAnn NotPromoted a (noLoc eqTyCon_RDR) b
#endif
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
  let decs = lets <> map (noLoc . decFromBinding dflags) binds

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
#if __GLASGOW_HASKELL__ >= 900 && __GLASGOW_HASKELL__ < 906
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
#if __GLASGOW_HASKELL__ < 902
  liftIO $ Err.warningMsg dflags sdoc
#elif __GLASGOW_HASKELL__ >= 902 && __GLASGOW_HASKELL__ < 904
  logger <- GHC.getLogger
  liftIO $ Err.warningMsg logger dflags sdoc
#else
  logger <- GHC.getLogger
  let
    diagOpts = GHC.initDiagOpts dflags
    mc = Err.mkMCDiagnostic diagOpts GHC.WarningWithoutFlag
#if __GLASGOW_HASKELL__ >= 906
           Nothing
#endif
  liftIO $ GHC.logMsg logger mc noSrcSpan sdoc
#endif

-- | The actual implementation.
pluginImpl ::
  (?nms :: ExternalNames) => [GHC.CommandLineOption] -> GHC.ModSummary ->
#if __GLASGOW_HASKELL__ < 904
  GHC.HsParsedModule -> GHC.Hsc GHC.HsParsedModule
#else
  GHC.ParsedResult -> GHC.Hsc GHC.ParsedResult
#endif
pluginImpl cliOptions _modSummary m = do
    -- cli options are activated by -fplugin-opt=CircuitNotation:debug
    debug <- case cliOptions of
      []        -> pure False
      ["debug"] -> pure True
      _ -> do
        warningMsg $ Outputable.text $ "CircuitNotation: unknown cli options " <> show cliOptions
        pure False
    hpm_module' <- do
#if __GLASGOW_HASKELL__ < 904
      transform debug (GHC.hpm_module m)
    let module' = m { GHC.hpm_module = hpm_module' }
#else
      transform debug $ GHC.hpm_module $ GHC.parsedResultModule m
    let parsedResultModule' = (GHC.parsedResultModule m)
                                { GHC.hpm_module = hpm_module' }
        module' = m { GHC.parsedResultModule = parsedResultModule' }
#endif
    return module'

-- Debugging functions -------------------------------------------------

ppr :: GHC.Outputable a => a -> CircuitM ()
ppr a = do
  dflags <- GHC.getDynFlags
  liftIO $ putStrLn (GHC.showPpr dflags a)

showC :: Data.Data a => a -> String
showC a = show (typeOf a) <> " " <> show (Data.toConstr a)

-- Names ---------------------------------------------------------------

fwdNames :: [String]
fwdNames = ["Fwd", "Signal"]

-- | Collection of names external to circuit-notation.
data ExternalNames = ExternalNames
  { circuitCon :: GHC.RdrName
  , runCircuitName :: GHC.RdrName
  , tagBundlePat :: GHC.RdrName
  , tagName :: GHC.RdrName
  , tagTName :: GHC.RdrName
  , fwdBwdCon :: GHC.RdrName
  , fwdAndBwdTypes :: Direction -> GHC.RdrName
  , trivialBwd :: GHC.RdrName
  , consPat :: GHC.RdrName
  }

defExternalNames :: ExternalNames
defExternalNames = ExternalNames
  { circuitCon = GHC.Unqual (OccName.mkDataOcc "TagCircuit")
  , runCircuitName = GHC.Unqual (OccName.mkVarOcc "runTagCircuit")
  , tagBundlePat = GHC.Unqual (OccName.mkDataOcc "BusTagBundle")
  , tagName = GHC.Unqual (OccName.mkDataOcc "BusTag")
  , tagTName = GHC.Unqual (OccName.mkTcOcc "BusTag")
  , fwdBwdCon = GHC.Unqual (OccName.mkDataOcc ":->")
  , fwdAndBwdTypes = \case
      Fwd -> GHC.Unqual (OccName.mkTcOcc "Fwd")
      Bwd -> GHC.Unqual (OccName.mkTcOcc "Bwd")
  , trivialBwd = GHC.Unqual (OccName.mkVarOcc "unitBwd")
#if __GLASGOW_HASKELL__ > 900
  , consPat = GHC.Unqual (OccName.mkDataOcc ":>!")
#else
  , consPat = GHC.Unqual (OccName.mkDataOcc ":>")
#endif
  }
