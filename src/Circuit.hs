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

module Circuit where

-- | Infinite sequence of values.
data Signal a = a :- Signal a
  deriving Functor

instance Applicative Signal where
  pure a = a :- pure a
  (f :- fs) <*> (a :- as) = f a :- (fs <*> as)

type family M2S a
type family S2M a

-- | The identity circuit.
idC :: Circuit a a
idC = Circuit id

data DF a
data DFM2S a = DFM2S Bool a
newtype DFS2M = DFS2M Bool

type instance M2S (DF a) = Signal (DFM2S a)
type instance S2M (DF a) = Signal DFS2M

type instance M2S [a] = [M2S a]
type instance S2M [a] = [S2M a]

type instance M2S () = ()
type instance S2M () = ()

type instance M2S (a,b) = (M2S a, M2S b)
type instance S2M (a,b) = (S2M a, S2M b)

type instance M2S (a,b,c) = (M2S a, M2S b, M2S c)
type instance S2M (a,b,c) = (S2M a, S2M b, S2M c)

type instance M2S (Signal a) = Signal a
type instance S2M (Signal a) = ()

-- | Circuit type.
newtype Circuit a b = Circuit {runCircuit :: (M2S a, S2M b) -> (M2S b, S2M a)}
type CircuitT a b = (M2S a, S2M b) -> (M2S b, S2M a)
