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
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE TypeOperators       #-}

module Circuit where

import           Clash.Prelude

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

type instance Fwd (Signal dom a) = Signal dom a
type instance Bwd (Signal dom a) = ()

-- | Circuit type.
newtype Circuit a b = Circuit { runCircuit :: CircuitT a b }
type CircuitT a b = (Fwd a :-> Bwd b) -> (Bwd a :-> Fwd b)

class TrivialBwd a where
  unitBwd :: a

instance TrivialBwd () where
  unitBwd = ()

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
