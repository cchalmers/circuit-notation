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

{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DefaultSignatures        #-}
{-# LANGUAGE TypeFamilyDependencies        #-}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE GADTs        #-}

module Circuit where

import Data.Default
import GHC.TypeLits

data Domain

-- | Infinite sequence of values.
data Signal (dom :: Domain) a = a :- Signal dom a
  deriving Functor

instance Default a => Default (Signal dom a) where
  def = pure def

instance Applicative (Signal dom) where
  pure a = a :- pure a
  (f :- fs) <*> (a :- as) = f a :- (fs <*> as)

type family M2S a
type family S2M a

-- | The identity circuit.
idC :: Circuit a a
idC = Circuit id

data DF (dom :: Domain)  a
data DFM2S a = DFM2S Bool a
newtype DFS2M = DFS2M Bool

instance Default (DFM2S a) where
  def = DFM2S False (error "error default")
instance Default DFS2M where
  def = DFS2M True

type instance M2S (DF dom a) = Signal dom (DFM2S a)
type instance S2M (DF dom a) = Signal dom DFS2M

data Vec n a where
  Nil :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (n + 1) a

myVec :: Vec 2 Int
myVec = Cons 1 (Cons 2 Nil)

type instance M2S (Vec n a) = Vec n (M2S a)
type instance S2M (Vec n a) = Vec n (S2M a)

type instance M2S [a] = [M2S a]
type instance S2M [a] = [S2M a]

type instance M2S () = ()
type instance S2M () = ()

type instance M2S (a,b) = (M2S a, M2S b)
type instance S2M (a,b) = (S2M a, S2M b)

type instance M2S (a,b,c) = (M2S a, M2S b, M2S c)
type instance S2M (a,b,c) = (S2M a, S2M b, S2M c)

type instance M2S (Signal dom a) = Signal dom a
type instance S2M (Signal dom a) = ()

-- | Circuit type.
newtype Circuit a b = Circuit {runCircuit :: (M2S a, S2M b) -> (M2S b, S2M a)}
type CircuitT a b = (M2S a, S2M b) -> (M2S b, S2M a)

class Bundle a where
  type Unbundled (dom :: Domain) a = res | res -> dom a
  type Unbundled dom a = Signal dom a
  -- | Example:
  --
  -- @
  -- __bundle__ :: ('Signal' dom a, 'Signal' dom b) -> 'Signal' dom (a,b)
  -- @
  --
  -- However:
  --
  -- @
  -- __bundle__ :: 'Signal' dom 'Clash.Sized.BitVector.Bit' -> 'Signal' dom 'Clash.Sized.BitVector.Bit'
  -- @
  bundle :: Unbundled dom a -> Signal dom a

  {-# INLINE bundle #-}
  default bundle :: (Signal dom a ~ Unbundled dom a)
                 => Unbundled dom a -> Signal dom a
  bundle s = s
  -- | Example:
  --
  -- @
  -- __unbundle__ :: 'Signal' dom (a,b) -> ('Signal' dom a, 'Signal' dom b)
  -- @
  --
  -- However:
  --
  -- @
  -- __unbundle__ :: 'Signal' dom 'Clash.Sized.BitVector.Bit' -> 'Signal' dom 'Clash.Sized.BitVector.Bit'
  -- @
  unbundle :: Signal dom a -> Unbundled dom a

  {-# INLINE unbundle #-}
  default unbundle :: (Unbundled dom a ~ Signal dom a)
                   => Signal dom a -> Unbundled dom a
  unbundle s = s

instance Bundle ()
instance Bundle Bool
instance Bundle Integer
instance Bundle Int
instance Bundle Float
instance Bundle Double
instance Bundle (Maybe a)
instance Bundle (Either a b)

instance Bundle (a1, a2) where
  type Unbundled dom (a1, a2) = (Signal dom a1, Signal dom a2)
  bundle = zip2S
  unbundle = unzip2S

instance Bundle (a1, a2, a3) where
  type Unbundled dom (a1, a2, a3) = (Signal dom a1, Signal dom a2, Signal dom a3)
  bundle = zip3S
  unbundle = unzip3S

-- instance Bundle Bit
-- instance Bundle (BitVector n)
-- instance Bundle (Index n)
-- instance Bundle (Fixed rep int frac)
-- instance Bundle (Signed n)
-- instance Bundle (Unsigned n)

zip2S :: (Signal dom a, Signal dom b) -> Signal dom (a, b)
zip2S (a :- as, b :- bs) = (a, b) :- zip2S (as, bs)

zip3S :: (Signal dom a, Signal dom b, Signal dom c) -> Signal dom (a, b, c)
zip3S (a :- as, b :- bs, c :- cs) = (a, b, c) :- zip3S (as, bs, cs)

unzip2S :: Signal dom (a, b) -> (Signal dom a, Signal dom b)
unzip2S ((a, b) :- asbs) =
  let ~(as, bs) = unzip2S asbs
  in  (a :- as, b :- bs)

unzip3S :: Signal dom (a, b, c) -> (Signal dom a, Signal dom b, Signal dom c)
unzip3S ((a, b, c) :- asbscs) =
  let ~(as, bs, cs) = unzip3S asbscs
  in  (a :- as, b :- bs, c :- cs)
