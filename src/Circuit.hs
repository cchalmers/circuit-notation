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

{-# LANGUAGE CPP                    #-}
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

#if __GLASGOW_HASKELL__ > 900
-- | Unsafe version of ':>'. Will fail if applied to empty vectors. This is used to
-- workaround spurious incomplete pattern match warnings generated in newer GHC
-- versions.
pattern (:>!) :: a -> Vec n a -> Vec (n + 1) a
pattern (:>!) x xs <- (\ys -> (head ys, tail ys) -> (x,xs))
{-# COMPLETE (:>!) #-}
infixr 5 :>!
#endif

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

-- | For /dev/null-like circuits: always acknowledge incoming data
--   while never sending out data. Used for ignoring streams with an underscore prefix.
class DriveVoid a where
  driveVoid :: a

instance DriveVoid () where
  driveVoid = ()

instance (DriveVoid a) => DriveVoid (Signal dom a) where
  driveVoid = pure driveVoid

instance DriveVoid (DFM2S a) where
  driveVoid = DFM2S False (error "void")

instance DriveVoid DFS2M where
  driveVoid = DFS2M True

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

type instance Fwd (Signal dom a) = Signal dom a
type instance Bwd (Signal dom a) = ()

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

instance BusTagBundle (Vec n t) (Vec n a) where
  type BusTagUnbundled (Vec n t) (Vec n a) = Vec n (BusTag t a)
  taggedBundle = BusTag . fmap unBusTag
  taggedUnbundle = fmap BusTag . unBusTag

pattern BusTagBundle :: BusTagBundle t a => BusTagUnbundled t a -> BusTag t a
pattern BusTagBundle a <- (taggedUnbundle -> a) where
  BusTagBundle a = taggedBundle a
{-# COMPLETE BusTagBundle #-}
