{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveFunctor #-}

module Circuit where

data Signal a = a :- Signal a
  deriving Functor

instance Applicative Signal where
  pure a = a :- pure a
  (f :- fs) <*> (a :- as) = f a :- (fs <*> as)

type family M2S a
type family S2M a

idC :: Circuit a a
idC = Circuit id

data DF a
data DFM2S a = DFM2S Bool a
data DFS2M = DFS2M Bool

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

-- idC :: Int
-- idC = 5

-- data DF d a

-- myCircuit :: Int
-- myCircuit = circuit \(v1 :: DF d a) (v3 :: blah) -> do
--   v1' <- total -< (v3 :: DF domain Int)
--   v2 <- total -< (v1 :: DF domain Int)
--   -- v2' <- total2 -< v2
--   -- v3 <- zipC -< (v1', v2')
--   idC -< v3

-- Circuit (() -> a)


-- Circuit (a -> b -> c)
-- Circuit ((a,b) -> c)
-- Circuit (a)

-- (><) :: Circuit (a -> b -> c) -> Circuit a -> Circuit (b -> c)

data Circuit a b = Circuit {runCircuit :: (M2S a, S2M b) -> (M2S b, S2M a)}
type CircuitT a b = (M2S a, S2M b) -> (M2S b, S2M a)
