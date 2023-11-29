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


type TagCircuitT a b = (TagFwd a :-> TagBwd b) -> (TagBwd a :-> TagFwd b)

newtype Tag t b = Tag {unTag :: b}

type TagFwd a = Tag a (Fwd a)
type TagBwd a = Tag a (Bwd a)

mkTagCircuit :: TagCircuitT a b -> Circuit a b
mkTagCircuit f = Circuit $ \ (aFwd :-> bBwd) -> let
    (Tag aBwd :-> Tag bFwd) = f (Tag aFwd :-> Tag bBwd)
  in (aBwd :-> bFwd)

runTagCircuit :: Circuit a b -> TagCircuitT a b
runTagCircuit (Circuit c) (aFwd :-> bBwd) = let
    (aBwd :-> bFwd) = c (unTag aFwd :-> unTag bBwd)
  in (Tag aBwd :-> Tag bFwd)

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

instance TrivialBwd a => TrivialBwd (Tag t a) where
  unitBwd = Tag unitBwd


class TagBundle t a where
  type TagUnbundled t a = res | res -> t a
  taggedBundle :: TagUnbundled t a -> Tag t a
  taggedUnbundle :: Tag t a -> TagUnbundled t a

instance TagBundle (ta, tb) (a, b) where
  type TagUnbundled (ta, tb) (a, b) = (Tag ta a, Tag tb b)
  taggedBundle (Tag a, Tag b) = Tag (a, b)
  taggedUnbundle (Tag (a, b)) =  (Tag a, Tag b)

instance TagBundle (ta, tb, tc) (a, b, c) where
  type TagUnbundled (ta, tb, tc) (a, b, c) = (Tag ta a, Tag tb b, Tag tc c)
  taggedBundle (Tag a, Tag b, Tag c) = Tag (a, b, c)
  taggedUnbundle (Tag (a, b, c)) =  (Tag a, Tag b, Tag c)

instance TagBundle (Vec n t) (Vec n a) where
  type TagUnbundled (Vec n t) (Vec n a) = Vec n (Tag t a)
  taggedBundle = Tag . fmap unTag
  taggedUnbundle = fmap Tag . unTag

pattern TagBundle :: TagBundle t a => TagUnbundled t a -> Tag t a
pattern TagBundle a <- (taggedUnbundle -> a) where
  TagBundle a = taggedBundle a

instance TagBundle () () where
  type TagUnbundled () () = ()
  taggedBundle = Tag
  taggedUnbundle = unTag
