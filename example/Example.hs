{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

This file contains examples of using the Circuit Notation.
-}

{-# LANGUAGE Arrows              #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE DataKinds        #-}

{-# OPTIONS -fplugin=CircuitNotation #-}
{-# OPTIONS -fplugin-opt=CircuitNotation:debug #-}
{-# OPTIONS -Wall #-}


---- | Hack idiom-brackets using Source Plugin.
----
---- As nobody (?) writes their lists as `([1, 2, 3])`,
---- we can steal that syntax!
---- module Main (main) where

module Example where

import Circuit

import Clash.Prelude (Signal, Vec(..))

idCircuit :: Circuit a a
idCircuit = idC

swapC :: Circuit (a,b) (b,a)
swapC = id $ circuit $ \ ~(a,b) -> ~(b,a)

circuitA :: Circuit () (DF domain Int)
circuitA = Circuit (\_ -> () :-> pure (DFM2S True 3))

circuitB :: Circuit () (Signal domain Int)
circuitB = Circuit (\_ -> () :-> pure 3)

circuitC :: Circuit (Signal domain Int) (DF domain Int)
circuitC = Circuit (\(as :-> _) -> () :-> DFM2S True <$> as)

noLambda :: Circuit () (DF domain Int)
noLambda = circuit $ do
  i <- circuitA
  idC -< i

-- noLambda =
--   let
--     inferenceHelper ::
--       () =>
--       ((Circuit () iTy -> CircuitT () iTy) -> CircuitT () iTy)
--       -> Circuit () iTy
--     inferenceHelper = \ f -> Circuit (f runCircuit)
--   in
--     inferenceHelper
--       (\ run0 (~() :-> i_Bwd)
--         -> let () :-> i_Fwd = run0 circuitA (() :-> i_Bwd)
--             in () :-> i_Fwd)


sigExpr :: Signal domain Int -> Circuit () (DF domain Int)
sigExpr sig = circuit do
  i <- circuitC -< Signal sig
  idC -< i

-- sigPat :: (( Signal Int -> Signal Int ))
sigPat :: Circuit (Signal domain Int) (Signal domain Int)
sigPat = circuit $ \(Signal a) -> do
  i <- (idC :: Circuit (Signal domain Int) (Signal domain Int)) -< Signal a
  idC -< i

sigPat2 :: Circuit (Signal dom Int) (Signal dom Int)
sigPat2 = circuit $ \(Signal a) -> do
  i <- (idC :: Circuit (Signal dom Int) (Signal dom Int)) -< Signal a
  idC -< i

fstC :: Circuit (Signal domain a, Signal domain b) (Signal domain a)
fstC = circuit $ \(a, _b) -> do idC -< a

fstC2 :: Circuit (Signal domain a, Signal domain b) (Signal domain a)
fstC2 = circuit $ \ab -> do
  (a, _b) <- idC -< ab
  idC -< a

fstC3 :: Circuit (Signal domain a, Signal domain b) (Signal domain a)
fstC3 = circuit \(a, _b) -> a

unfstC :: Circuit (DF domain a) (DF domain a, DF domain b)
unfstC = circuit $ \a -> do
  idC -< (a, _b)

unfstC2 :: Circuit (DF domain a) (DF domain a, DF domain b)
unfstC2 = circuit $ \a -> do
  ab <- circuit (\(aa,bb) -> (bb,aa)) -< (_b, a)
  idC -< ab

unfstC3 :: Circuit (DF dom a) (DF dom a, DF dom b)
unfstC3 = circuit $ \a -> do
  ab <- idC -< (a, _b)
  ab' <- idC -< ab
  idC -< ab'


swapTest :: forall a b. Circuit (a,b) (b,a)
-- swapTest = circuit $ \(a,b) -> (idCircuit :: Circuit (b, a) (b, a)) -< (b, a)
swapTest = circuit $ \(a,b) -> do idC -< (b, a)

unvecC :: Circuit (Vec 2 a) (a, a)
unvecC = circuit \ ~[x,y] -> (x, y)

vecC :: Circuit (a, a) (Vec 2 a)
vecC = circuit \(x, y) -> [x,y]

vec0 :: Circuit (Vec 0 a) ()
vec0 = circuit \[] -> ()

vec00 :: Circuit (Vec 0 a) (Vec 0 a)
vec00 = circuit \[] -> []


-- -- myDesire :: Circuit Int Char
-- -- myDesire = Circuit (\(aM2S,bS2M) -> let
-- --   (aM2S', bS2M') = runCircuit myCircuit (aM2S, bS2M)
-- --   in (aM2S', bS2M'))

-- -- var :: (Int, Int)
-- -- var = (3, 5)

-- -- myLet :: Int
-- -- myLet = let (yo, yo') = var in yo

-- -- ah :: (Int,Int)
-- -- ah = (7,11)

-- -- tupCir1 :: Circuit (Int, Char) (Char, Int)
-- -- tupCir1 = circuit \ input -> do
-- --   (c,i) <- swapC @Int -< input
-- --   i' <- myCircuit -< [i]
-- --   let myIdCircuit = circuit \port -> port
-- --   c' <- myCircuitRev -< c
-- --   c'' <- myIdCircuit -< c'
-- --   idC -< (i', c'')

-- tupleCircuit :: Circuit Int Char
-- tupleCircuit = id $ circuit \a -> do
--   let b = 3
--   b <- (circuit \a -> do b <- myCircuit -< a;idC -< b) -< a
--   a' <- myCircuitRev -< b
--   b' <- myCircuit -< a'
--   b'' <- (circuit \aa -> do idC -< aa) -< b'
--   idC -< b''

-- -- simpleCircuit :: Circuit Int Char
-- -- simpleCircuit = id $ circuit \a -> do
-- --   b <- (circuit \a -> do b <- myCircuit -< a;idC -< b) -< a
-- --   a' <- myCircuitRev -< b
-- --   b' <- myCircuit -< a'
-- --   b'' <- (circuit \aa -> do idC -< aa) -< b'
-- --   idC -< b''

-- myCircuit :: Int
-- myCircuit = circuit \(v1 :: DF d a) (v3 :: blah) -> do
--   v1' <- total -< (v3 :: DF domain Int) -< (v4 :: DF domain Int)
--   v2 <- total -< v1
--   let a = b
--   -- v2' <- total2 -< v2
--   -- v3 <- zipC -< (v1', v2')
--   v1 <- idC -< v3

-- -- type RunCircuit a b = (Circuit a b -> (M2S a, S2M b) -> (M2S b, S2M a))
-- -- type CircuitId a b = Circuit a b -> Circuit a b

-- -- myCircuit = let
-- --   _circuits :: (RunCircuit a b, RunCircuit c d, RunCircuit (b,d) e, CircuitId (a,c) e)
-- --   _circuits@(runC1, runC2, runC2, cId) = (runCircuit, runCircuit, runCircuit, id)

-- --   in cId $ Circuit $ \((v1M2S, v2M2S),outputS2M) -> let

-- --   (v1'M2S, v1S2M) = runC1 total (v1M2s, v1'S2M)
-- --   (v2'M2S, v2S2M) = runC2 total2 (v2M2s, v2'S2M)
-- --   (v3M2S, (v1'S2M, v2'S2M)) = runC3 zipC ((v1'M2S, v2'M2S), v3S2M)

-- --   in (v3M2S, (v1S2M, v2S2M))




--   -- circuitHelper
--   --   :: Circuit a b
--   --   -> Circuit c d
--   --   -> Circuit (b,d) e


-- -- myCircuit :: Int
-- -- myCircuit = circuit (\(v1,v2) -> (v2,v1))

-- -- myCircuit :: Int
-- -- myCircuit = circuit do
-- --   (v2,v1) <- yeah
-- --   idC -< (v1, v2)

-- -- myCircuit = proc v1 -> do
-- --   x <- total -< value
--   -- fin -< a
--   -- idC -< (t / n)
