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
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ViewPatterns        #-}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE GADTs        #-}

module Circuit where

import Data.Default
import GHC.TypeLits
import Unsafe.Coerce

data Domain

-- | Infinite sequence of values.
data Signal (dom :: Domain) a = a :- Signal dom a
  deriving Functor

instance Default a => Default (Signal dom a) where
  def = pure def

instance Applicative (Signal dom) where
  pure a = a :- pure a
  (f :- fs) <*> (a :- as) = f a :- (fs <*> as)

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

data Vec n a where
  Nil :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (n + 1) a

headV :: Vec (n + 1) a -> a
headV (x `Cons` _) = x
headV Nil = error ""
tailV :: forall n a. Vec (n + 1) a -> Vec n a
tailV (_ `Cons` xs) = unsafeCoerce xs
tailV Nil = error ""

pattern (:>) :: a -> Vec n a -> Vec (n + 1) a
pattern (:>) x xs <- ((\ys -> (headV ys, tailV ys)) -> (x,xs))
  where
      (:>) x xs = Cons x xs
infixr 5 :>

myVec :: Vec 2 Int
myVec = 1 :> 2 :> Nil

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
