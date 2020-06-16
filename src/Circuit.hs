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
