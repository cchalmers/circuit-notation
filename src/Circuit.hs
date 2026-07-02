{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

This file contains the 'Circuit' type, that the notation describes.
-}

{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE NoImplicitPrelude      #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ViewPatterns           #-}

module Circuit where

import           Clash.Prelude

-- | Unsafe version of ':>'. Will fail if applied to empty vectors. This is used to
-- workaround spurious incomplete pattern match warnings generated in newer GHC
-- versions.
pattern (:>!) :: a -> Vec n a -> Vec (n + 1) a
pattern (:>!) x xs <- (\ys -> (head ys, tail ys) -> (x,xs))
{-# COMPLETE (:>!) #-}
infixr 5 :>!

type family Fwd a
type family Bwd a

infixr 0 :->
-- | A type to symbolise arguments going to results of a circuit.
data (a :-> b) = a :-> b
  deriving (Show, Eq)

-- | The identity circuit.
idC :: Circuit a a
idC = Circuit $ \(aFwd :-> aBwd) -> aBwd :-> aFwd

data DF (dom :: Domain)  a
data DFM2S a = DFM2S Bool a
newtype DFS2M = DFS2M Bool

instance Default (DFM2S a) where
  def = DFM2S False (error "error default")
instance Default DFS2M where
  def = DFS2M True

type instance Fwd (DF dom a) = Signal dom (DFM2S a)
type instance Bwd (DF dom a) = Signal dom DFS2M

type instance Fwd (Vec n a) = Vec n (Fwd a)
type instance Bwd (Vec n a) = Vec n (Bwd a)

type instance Fwd [a] = [Fwd a]
type instance Bwd [a] = [Bwd a]

type instance Fwd () = ()
type instance Bwd () = ()

type instance Fwd (a,b) = (Fwd a, Fwd b)
type instance Bwd (a,b) = (Bwd a, Bwd b)

type instance Fwd (a,b,c) = (Fwd a, Fwd b, Fwd c)
type instance Bwd (a,b,c) = (Bwd a, Bwd b, Bwd c)

type instance Fwd (a,b,c,d) = (Fwd a, Fwd b, Fwd c, Fwd d)
type instance Bwd (a,b,c,d) = (Bwd a, Bwd b, Bwd c, Bwd d)

type instance Fwd (a,b,c,d,e) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e)
type instance Bwd (a,b,c,d,e) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e)

type instance Fwd (a,b,c,d,e,f) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f)
type instance Bwd (a,b,c,d,e,f) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f)

type instance Fwd (a,b,c,d,e,f,g) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f, Fwd g)
type instance Bwd (a,b,c,d,e,f,g) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f, Bwd g)

type instance Fwd (a,b,c,d,e,f,g,h) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f, Fwd g, Fwd h)
type instance Bwd (a,b,c,d,e,f,g,h) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f, Bwd g, Bwd h)

type instance Fwd (a,b,c,d,e,f,g,h,i) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f, Fwd g, Fwd h, Fwd i)
type instance Bwd (a,b,c,d,e,f,g,h,i) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f, Bwd g, Bwd h, Bwd i)

type instance Fwd (a,b,c,d,e,f,g,h,i,j) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f, Fwd g, Fwd h, Fwd i, Fwd j)
type instance Bwd (a,b,c,d,e,f,g,h,i,j) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f, Bwd g, Bwd h, Bwd i, Bwd j)

type instance Fwd (a,b,c,d,e,f,g,h,i,j,k) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f, Fwd g, Fwd h, Fwd i, Fwd j, Fwd k)
type instance Bwd (a,b,c,d,e,f,g,h,i,j,k) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f, Bwd g, Bwd h, Bwd i, Bwd j, Bwd k)

type instance Fwd (a,b,c,d,e,f,g,h,i,j,k,l) = (Fwd a, Fwd b, Fwd c, Fwd d, Fwd e, Fwd f, Fwd g, Fwd h, Fwd i, Fwd j, Fwd k, Fwd l)
type instance Bwd (a,b,c,d,e,f,g,h,i,j,k,l) = (Bwd a, Bwd b, Bwd c, Bwd d, Bwd e, Bwd f, Bwd g, Bwd h, Bwd i, Bwd j, Bwd k, Bwd l)

type instance Fwd (Signal dom a) = Signal dom a
type instance Bwd (Signal dom a) = ()

type instance Fwd (DSignal dom d a) = DSignal dom d a
type instance Bwd (DSignal dom d a) = ()

-- | Circuit type.
newtype Circuit a b = Circuit { runCircuit :: CircuitT a b }
type CircuitT a b = (Fwd a :-> Bwd b) -> (Bwd a :-> Fwd b)


type TagCircuitT a b = (BusTag a (Fwd a) :-> BusTag b (Bwd b)) -> (BusTag a (Bwd a) :-> BusTag b (Fwd b))

newtype BusTag t b = BusTag {unBusTag :: b}

mkTagCircuit :: TagCircuitT a b -> Circuit a b
mkTagCircuit f = Circuit $ \ (aFwd :-> bBwd) -> let
    (BusTag aBwd :-> BusTag bFwd) = f (BusTag aFwd :-> BusTag bBwd)
  in (aBwd :-> bFwd)

runTagCircuit :: Circuit a b -> TagCircuitT a b
runTagCircuit (Circuit c) (aFwd :-> bBwd) = let
    (aBwd :-> bFwd) = c (unBusTag aFwd :-> unBusTag bBwd)
  in (BusTag aBwd :-> BusTag bFwd)

pattern TagCircuit :: TagCircuitT a b -> Circuit a b
pattern TagCircuit f <- (runTagCircuit -> f) where
  TagCircuit f = mkTagCircuit f


class TrivialBwd a where
  unitBwd :: a

instance TrivialBwd () where
  unitBwd = ()

instance (TrivialBwd a) => TrivialBwd (Signal dom a) where
  unitBwd = pure unitBwd

instance (TrivialBwd a, KnownNat n) => TrivialBwd (Vec n a) where
  unitBwd = repeat unitBwd

instance (TrivialBwd a, TrivialBwd b) => TrivialBwd (a,b) where
  unitBwd = (unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c) => TrivialBwd (a,b,c) where
  unitBwd = (unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d) => TrivialBwd (a,b,c,d) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e) => TrivialBwd (a,b,c,d,e) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f) => TrivialBwd (a,b,c,d,e,f) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f, TrivialBwd g) => TrivialBwd (a,b,c,d,e,f,g) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f, TrivialBwd g, TrivialBwd h) => TrivialBwd (a,b,c,d,e,f,g,h) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f, TrivialBwd g, TrivialBwd h, TrivialBwd i) => TrivialBwd (a,b,c,d,e,f,g,h,i) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f, TrivialBwd g, TrivialBwd h, TrivialBwd i, TrivialBwd j) => TrivialBwd (a,b,c,d,e,f,g,h,i,j) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f, TrivialBwd g, TrivialBwd h, TrivialBwd i, TrivialBwd j, TrivialBwd k) => TrivialBwd (a,b,c,d,e,f,g,h,i,j,k) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance (TrivialBwd a, TrivialBwd b, TrivialBwd c, TrivialBwd d, TrivialBwd e, TrivialBwd f, TrivialBwd g, TrivialBwd h, TrivialBwd i, TrivialBwd j, TrivialBwd k, TrivialBwd l) => TrivialBwd (a,b,c,d,e,f,g,h,i,j,k,l) where
  unitBwd = (unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd, unitBwd)

instance TrivialBwd a => TrivialBwd (BusTag t a) where
  unitBwd = BusTag unitBwd

class BusTagBundle t a where
  type BusTagUnbundled t a = res | res -> t a
  taggedBundle :: BusTagUnbundled t a -> BusTag t a
  taggedUnbundle :: BusTag t a -> BusTagUnbundled t a

instance BusTagBundle () () where
  type BusTagUnbundled () () = ()
  taggedBundle = BusTag
  taggedUnbundle = unBusTag

instance BusTagBundle (ta, tb) (a, b) where
  type BusTagUnbundled (ta, tb) (a, b) = (BusTag ta a, BusTag tb b)
  taggedBundle (BusTag a, BusTag b) = BusTag (a, b)
  taggedUnbundle (BusTag (a, b)) =  (BusTag a, BusTag b)

instance BusTagBundle (ta, tb, tc) (a, b, c) where
  type BusTagUnbundled (ta, tb, tc) (a, b, c) = (BusTag ta a, BusTag tb b, BusTag tc c)
  taggedBundle (BusTag a, BusTag b, BusTag c) = BusTag (a, b, c)
  taggedUnbundle (BusTag (a, b, c)) =  (BusTag a, BusTag b, BusTag c)

instance BusTagBundle (ta, tb, tc, td) (a, b, c, d) where
  type BusTagUnbundled (ta, tb, tc, td) (a, b, c, d) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d) = BusTag (a, b, c, d)
  taggedUnbundle (BusTag (a, b, c, d)) =  (BusTag a, BusTag b, BusTag c, BusTag d)

instance BusTagBundle (ta, tb, tc, td, te) (a, b, c, d, e) where
  type BusTagUnbundled (ta, tb, tc, td, te) (a, b, c, d, e) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e) = BusTag (a, b, c, d, e)
  taggedUnbundle (BusTag (a, b, c, d, e)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e)

instance BusTagBundle (ta, tb, tc, td, te, tf) (a, b, c, d, e, f) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf) (a, b, c, d, e, f) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f) = BusTag (a, b, c, d, e, f)
  taggedUnbundle (BusTag (a, b, c, d, e, f)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f)

instance BusTagBundle (ta, tb, tc, td, te, tf, tg) (a, b, c, d, e, f, g) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf, tg) (a, b, c, d, e, f, g) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f, BusTag tg g)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g) = BusTag (a, b, c, d, e, f, g)
  taggedUnbundle (BusTag (a, b, c, d, e, f, g)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g)

instance BusTagBundle (ta, tb, tc, td, te, tf, tg, th) (a, b, c, d, e, f, g, h) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf, tg, th) (a, b, c, d, e, f, g, h) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f, BusTag tg g, BusTag th h)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h) = BusTag (a, b, c, d, e, f, g, h)
  taggedUnbundle (BusTag (a, b, c, d, e, f, g, h)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h)

instance BusTagBundle (ta, tb, tc, td, te, tf, tg, th, ti) (a, b, c, d, e, f, g, h, i) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf, tg, th, ti) (a, b, c, d, e, f, g, h, i) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f, BusTag tg g, BusTag th h, BusTag ti i)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i) = BusTag (a, b, c, d, e, f, g, h, i)
  taggedUnbundle (BusTag (a, b, c, d, e, f, g, h, i)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i)

instance BusTagBundle (ta, tb, tc, td, te, tf, tg, th, ti, tj) (a, b, c, d, e, f, g, h, i, j) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf, tg, th, ti, tj) (a, b, c, d, e, f, g, h, i, j) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f, BusTag tg g, BusTag th h, BusTag ti i, BusTag tj j)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i, BusTag j) = BusTag (a, b, c, d, e, f, g, h, i, j)
  taggedUnbundle (BusTag (a, b, c, d, e, f, g, h, i, j)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i, BusTag j)

instance BusTagBundle (ta, tb, tc, td, te, tf, tg, th, ti, tj, tk) (a, b, c, d, e, f, g, h, i, j, k) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf, tg, th, ti, tj, tk) (a, b, c, d, e, f, g, h, i, j, k) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f, BusTag tg g, BusTag th h, BusTag ti i, BusTag tj j, BusTag tk k)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i, BusTag j, BusTag k) = BusTag (a, b, c, d, e, f, g, h, i, j, k)
  taggedUnbundle (BusTag (a, b, c, d, e, f, g, h, i, j, k)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i, BusTag j, BusTag k)

instance BusTagBundle (ta, tb, tc, td, te, tf, tg, th, ti, tj, tk, tl) (a, b, c, d, e, f, g, h, i, j, k, l) where
  type BusTagUnbundled (ta, tb, tc, td, te, tf, tg, th, ti, tj, tk, tl) (a, b, c, d, e, f, g, h, i, j, k, l) = (BusTag ta a, BusTag tb b, BusTag tc c, BusTag td d, BusTag te e, BusTag tf f, BusTag tg g, BusTag th h, BusTag ti i, BusTag tj j, BusTag tk k, BusTag tl l)
  taggedBundle (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i, BusTag j, BusTag k, BusTag l) = BusTag (a, b, c, d, e, f, g, h, i, j, k, l)
  taggedUnbundle (BusTag (a, b, c, d, e, f, g, h, i, j, k, l)) =  (BusTag a, BusTag b, BusTag c, BusTag d, BusTag e, BusTag f, BusTag g, BusTag h, BusTag i, BusTag j, BusTag k, BusTag l)

instance BusTagBundle (Vec n t) (Vec n a) where
  type BusTagUnbundled (Vec n t) (Vec n a) = Vec n (BusTag t a)
  taggedBundle = BusTag . fmap unBusTag
  taggedUnbundle = fmap BusTag . unBusTag

pattern BusTagBundle :: BusTagBundle t a => BusTagUnbundled t a -> BusTag t a
pattern BusTagBundle a <- (taggedUnbundle -> a) where
  BusTagBundle a = taggedBundle a
{-# COMPLETE BusTagBundle #-}

-- | A tagged 'Signal' bus. Used by the plugin for @Signal@ markers at the
-- value boundary of circuit blocks: matching or constructing with
-- 'SigTag' pins the bus type itself (the tag) to be a 'Signal', which
-- drives type inference. Since 'Fwd' is not injective, plain 'BusTag' would
-- leave the bus type ambiguous and type inference for nested circuits would
-- fail.
pattern SigTag :: Signal dom a -> BusTag (Signal dom a) (Signal dom a)
pattern SigTag s = BusTag s
{-# COMPLETE SigTag #-}

-- | Like 'SigTag' but for delayed signals, used for @DSignalV@ markers:
-- pins the bus type to be a 'DSignal', /including its delay index/. The
-- markers of one logic group all flow through one (delayed) bundle, so a
-- group's buses must agree on the delay as well as the domain — combining
-- values from different pipeline stages is rejected by the type checker.
-- Since the lifted logic is combinational, the group's outputs are produced
-- at the same delay its inputs are sampled at.
pattern DSigTag :: DSignal dom d a -> BusTag (DSignal dom d a) (DSignal dom d a)
pattern DSigTag s = BusTag s
{-# COMPLETE DSigTag #-}

-- | Buses whose forward channel carries a single value per clock cycle,
-- i.e. is convertible to a single 'Signal'. The @Fwd@ markers at the value
-- boundary of @circuit@ blocks work on any such bus: 'Signal's themselves,
-- 'Vec's and tuples of signal-like buses (all in the same domain), and any
-- custom bus given an instance.
class SignalBus t where
  type BusDom t :: Domain
  type SampleOf t
  -- | Sample the forward channel of a tagged bus as a signal of values.
  sigFromBus :: BusTag t (Fwd t) -> Signal (BusDom t) (SampleOf t)
  -- | Drive the forward channel of a tagged bus from a signal of values.
  sigToBus :: Signal (BusDom t) (SampleOf t) -> BusTag t (Fwd t)

instance SignalBus (Signal dom a) where
  type BusDom (Signal dom a) = dom
  type SampleOf (Signal dom a) = a
  sigFromBus = unBusTag
  sigToBus = BusTag

-- | A 'Vec' of signal-like buses is sampled as a 'Vec' of their values.
instance (SignalBus t, KnownNat n) => SignalBus (Vec n t) where
  type BusDom (Vec n t) = BusDom t
  type SampleOf (Vec n t) = Vec n (SampleOf t)
  sigFromBus (BusTag v) = bundle (map (\f -> sigFromBus (BusTag f :: BusTag t (Fwd t))) v)
  sigToBus s = BusTag (map (\x -> unBusTag (sigToBus x :: BusTag t (Fwd t))) (unbundle s))

instance (SignalBus a, SignalBus b, BusDom a ~ BusDom b) => SignalBus (a, b) where
  type BusDom (a, b) = BusDom a
  type SampleOf (a, b) = (SampleOf a, SampleOf b)
  sigFromBus (BusTag (fa, fb)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b)) )
  sigToBus vs = case unbundle vs of
    (va, vb) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b)) )

instance (SignalBus a, SignalBus b, SignalBus c, BusDom a ~ BusDom b, BusDom b ~ BusDom c)
    => SignalBus (a, b, c) where
  type BusDom (a, b, c) = BusDom a
  type SampleOf (a, b, c) = (SampleOf a, SampleOf b, SampleOf c)
  sigFromBus (BusTag (fa, fb, fc)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d )
    => SignalBus (a, b, c, d) where
  type BusDom (a, b, c, d) = BusDom a
  type SampleOf (a, b, c, d) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d)
  sigFromBus (BusTag (fa, fb, fc, fd)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e )
    => SignalBus (a, b, c, d, e) where
  type BusDom (a, b, c, d, e) = BusDom a
  type SampleOf (a, b, c, d, e) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e)
  sigFromBus (BusTag (fa, fb, fc, fd, fe)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f )
    => SignalBus (a, b, c, d, e, f) where
  type BusDom (a, b, c, d, e, f) = BusDom a
  type SampleOf (a, b, c, d, e, f) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f, SignalBus g
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f, BusDom f ~ BusDom g )
    => SignalBus (a, b, c, d, e, f, g) where
  type BusDom (a, b, c, d, e, f, g) = BusDom a
  type SampleOf (a, b, c, d, e, f, g) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f, SampleOf g)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff, fg)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f))
    , sigFromBus (BusTag fg :: BusTag g (Fwd g)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf, vg) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f))
      , unBusTag (sigToBus vg :: BusTag g (Fwd g)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f, SignalBus g, SignalBus h
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f, BusDom f ~ BusDom g, BusDom g ~ BusDom h )
    => SignalBus (a, b, c, d, e, f, g, h) where
  type BusDom (a, b, c, d, e, f, g, h) = BusDom a
  type SampleOf (a, b, c, d, e, f, g, h) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f, SampleOf g, SampleOf h)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff, fg, fh)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f))
    , sigFromBus (BusTag fg :: BusTag g (Fwd g))
    , sigFromBus (BusTag fh :: BusTag h (Fwd h)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf, vg, vh) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f))
      , unBusTag (sigToBus vg :: BusTag g (Fwd g))
      , unBusTag (sigToBus vh :: BusTag h (Fwd h)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f, SignalBus g, SignalBus h, SignalBus i
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f, BusDom f ~ BusDom g, BusDom g ~ BusDom h, BusDom h ~ BusDom i )
    => SignalBus (a, b, c, d, e, f, g, h, i) where
  type BusDom (a, b, c, d, e, f, g, h, i) = BusDom a
  type SampleOf (a, b, c, d, e, f, g, h, i) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f, SampleOf g, SampleOf h, SampleOf i)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff, fg, fh, fi)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f))
    , sigFromBus (BusTag fg :: BusTag g (Fwd g))
    , sigFromBus (BusTag fh :: BusTag h (Fwd h))
    , sigFromBus (BusTag fi :: BusTag i (Fwd i)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf, vg, vh, vi) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f))
      , unBusTag (sigToBus vg :: BusTag g (Fwd g))
      , unBusTag (sigToBus vh :: BusTag h (Fwd h))
      , unBusTag (sigToBus vi :: BusTag i (Fwd i)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f, SignalBus g, SignalBus h, SignalBus i, SignalBus j
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f, BusDom f ~ BusDom g, BusDom g ~ BusDom h, BusDom h ~ BusDom i, BusDom i ~ BusDom j )
    => SignalBus (a, b, c, d, e, f, g, h, i, j) where
  type BusDom (a, b, c, d, e, f, g, h, i, j) = BusDom a
  type SampleOf (a, b, c, d, e, f, g, h, i, j) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f, SampleOf g, SampleOf h, SampleOf i, SampleOf j)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff, fg, fh, fi, fj)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f))
    , sigFromBus (BusTag fg :: BusTag g (Fwd g))
    , sigFromBus (BusTag fh :: BusTag h (Fwd h))
    , sigFromBus (BusTag fi :: BusTag i (Fwd i))
    , sigFromBus (BusTag fj :: BusTag j (Fwd j)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf, vg, vh, vi, vj) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f))
      , unBusTag (sigToBus vg :: BusTag g (Fwd g))
      , unBusTag (sigToBus vh :: BusTag h (Fwd h))
      , unBusTag (sigToBus vi :: BusTag i (Fwd i))
      , unBusTag (sigToBus vj :: BusTag j (Fwd j)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f, SignalBus g, SignalBus h, SignalBus i, SignalBus j, SignalBus k
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f, BusDom f ~ BusDom g, BusDom g ~ BusDom h, BusDom h ~ BusDom i, BusDom i ~ BusDom j, BusDom j ~ BusDom k )
    => SignalBus (a, b, c, d, e, f, g, h, i, j, k) where
  type BusDom (a, b, c, d, e, f, g, h, i, j, k) = BusDom a
  type SampleOf (a, b, c, d, e, f, g, h, i, j, k) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f, SampleOf g, SampleOf h, SampleOf i, SampleOf j, SampleOf k)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff, fg, fh, fi, fj, fk)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f))
    , sigFromBus (BusTag fg :: BusTag g (Fwd g))
    , sigFromBus (BusTag fh :: BusTag h (Fwd h))
    , sigFromBus (BusTag fi :: BusTag i (Fwd i))
    , sigFromBus (BusTag fj :: BusTag j (Fwd j))
    , sigFromBus (BusTag fk :: BusTag k (Fwd k)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f))
      , unBusTag (sigToBus vg :: BusTag g (Fwd g))
      , unBusTag (sigToBus vh :: BusTag h (Fwd h))
      , unBusTag (sigToBus vi :: BusTag i (Fwd i))
      , unBusTag (sigToBus vj :: BusTag j (Fwd j))
      , unBusTag (sigToBus vk :: BusTag k (Fwd k)) )

instance
    ( SignalBus a, SignalBus b, SignalBus c, SignalBus d, SignalBus e, SignalBus f, SignalBus g, SignalBus h, SignalBus i, SignalBus j, SignalBus k, SignalBus l
    , BusDom a ~ BusDom b, BusDom b ~ BusDom c, BusDom c ~ BusDom d, BusDom d ~ BusDom e, BusDom e ~ BusDom f, BusDom f ~ BusDom g, BusDom g ~ BusDom h, BusDom h ~ BusDom i, BusDom i ~ BusDom j, BusDom j ~ BusDom k, BusDom k ~ BusDom l )
    => SignalBus (a, b, c, d, e, f, g, h, i, j, k, l) where
  type BusDom (a, b, c, d, e, f, g, h, i, j, k, l) = BusDom a
  type SampleOf (a, b, c, d, e, f, g, h, i, j, k, l) = (SampleOf a, SampleOf b, SampleOf c, SampleOf d, SampleOf e, SampleOf f, SampleOf g, SampleOf h, SampleOf i, SampleOf j, SampleOf k, SampleOf l)
  sigFromBus (BusTag (fa, fb, fc, fd, fe, ff, fg, fh, fi, fj, fk, fl)) = bundle
    ( sigFromBus (BusTag fa :: BusTag a (Fwd a))
    , sigFromBus (BusTag fb :: BusTag b (Fwd b))
    , sigFromBus (BusTag fc :: BusTag c (Fwd c))
    , sigFromBus (BusTag fd :: BusTag d (Fwd d))
    , sigFromBus (BusTag fe :: BusTag e (Fwd e))
    , sigFromBus (BusTag ff :: BusTag f (Fwd f))
    , sigFromBus (BusTag fg :: BusTag g (Fwd g))
    , sigFromBus (BusTag fh :: BusTag h (Fwd h))
    , sigFromBus (BusTag fi :: BusTag i (Fwd i))
    , sigFromBus (BusTag fj :: BusTag j (Fwd j))
    , sigFromBus (BusTag fk :: BusTag k (Fwd k))
    , sigFromBus (BusTag fl :: BusTag l (Fwd l)) )
  sigToBus vs = case unbundle vs of
    (va, vb, vc, vd, ve, vf, vg, vh, vi, vj, vk, vl) -> BusTag
      ( unBusTag (sigToBus va :: BusTag a (Fwd a))
      , unBusTag (sigToBus vb :: BusTag b (Fwd b))
      , unBusTag (sigToBus vc :: BusTag c (Fwd c))
      , unBusTag (sigToBus vd :: BusTag d (Fwd d))
      , unBusTag (sigToBus ve :: BusTag e (Fwd e))
      , unBusTag (sigToBus vf :: BusTag f (Fwd f))
      , unBusTag (sigToBus vg :: BusTag g (Fwd g))
      , unBusTag (sigToBus vh :: BusTag h (Fwd h))
      , unBusTag (sigToBus vi :: BusTag i (Fwd i))
      , unBusTag (sigToBus vj :: BusTag j (Fwd j))
      , unBusTag (sigToBus vk :: BusTag k (Fwd k))
      , unBusTag (sigToBus vl :: BusTag l (Fwd l)) )

-- | Like 'SigTag' but for any signal-like bus. Used by the plugin for @Fwd@
-- markers at the value boundary of @circuit@ blocks. Unlike 'SigTag' it
-- cannot drive type inference (several buses can share a forward type), so
-- the bus type has to be determined by context, e.g. the circuit's
-- signature or a concretely typed sub-circuit.
pattern FwdTag :: SignalBus t => Signal (BusDom t) (SampleOf t) -> BusTag t (Fwd t)
pattern FwdTag s <- (sigFromBus -> s) where
  FwdTag s = sigToBus s
{-# COMPLETE FwdTag #-}
