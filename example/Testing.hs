{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

For testing the circuit notation.
-}

{-# LANGUAGE Arrows                    #-}
{-# LANGUAGE BlockArguments            #-}
{-# LANGUAGE GADTs                     #-}
-- {-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE DataKinds       #-}

-- For testing:
{-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS -fplugin=CircuitNotation #-}
{-# OPTIONS -Wno-unused-local-binds #-}
{-# OPTIONS -Wno-missing-signatures #-}

module Example where

import           Circuit
-- import Data.Default

-- no c =
--   let
--     inferenceHelper ::
--       aTy ~ Int =>
--       Circuit (aTy, bTy) (b'Ty, a'Ty)
--       -> (Circuit aTy a'Ty -> CircuitT aTy a'Ty,
--           Circuit bTy b'Ty -> CircuitT bTy b'Ty)
--     cir
--       = Circuit $
--           \ ((a_M2S, b_M2S), (b'_S2M, a'_S2M))
--             -> let
--                 (a'_M2S, a_S2M) = run0 c (a_M2S, a'_S2M)
--                 (b'_M2S, b_S2M) = run1 c (b_M2S, b'_S2M)
--               in ((b'_M2S, a'_M2S), (a_S2M, b_S2M))
--     inferenceHelper = const (runCircuit, runCircuit)
--     (run0, run1) = inferenceHelper cir
--   in cir

-- swapIC :: Circuit Int Char -> Circuit (Int, Int) (Char, Char)
-- swapIC c = circuit $ \((a :: Int ,b) :: (Int, Int)) -> do
--   a' <- c -< a :: int
--   b' <- c -< b
--   idC -< (b',a')

-- fstC :: Circuit (Signal a, Signal b) (Signal a)
-- fstC = circuit $ \(a, _b) -> a

-- swapC :: Circuit (a,b) (b,a)
-- swapC = circuit $ \(a,b) -> (b,a)

unvecC :: Circuit (Vec 2 a) (a, a)
unvecC = circuit \[x,y] -> (x, y)

vecC :: Circuit (a, a) (Vec 2 a)
vecC = circuit \(x, y) -> [x,y]

vec0 :: Circuit (Vec 0 a) ()
vec0 = circuit \[] -> ()

vec00 :: Circuit (Vec 0 a) (Vec 0 a)
vec00 = circuit \[] -> []

sigPat :: Circuit (Signal Int) (Signal Int)
sigPat = circuit $ \(Signal a) -> do
  i <- (idC :: Circuit (Signal Int) (Signal Int)) -< Signal a
  idC -< i

-- unfstC2 :: Circuit (DF a) (DF a, DF b)
-- unfstC2 = let
--   inferenceHelper ::
--     ( (Circuit (aTy, _bTy) abTy -> CircuitT (aTy, _bTy) abTy)
--        -> CircuitT aTy abTy
--     ) -> Circuit aTy abTy
--   inferenceHelper = \f -> Circuit (f runCircuit)
--   in inferenceHelper \run0 (a_M2S, ab_S2M)
--           -> let
--                def_ = def
--                (ab_M2S, (a_S2M, _b_S2M)) = run0 idC ((a_M2S, def_), ab_S2M)
--              in (ab_M2S, a_S2M)

  -- inferenceHelper ::
  --   (CircuitT aTy abTy -> Circuit aTy abTy,
  --    Circuit (aTy, _bTy) abTy -> CircuitT (aTy, _bTy) abTy)
  -- inferenceHelper = (Circuit, runCircuit)
  -- (mkCircuit, run0) = inferenceHelper
  -- in mkCircuit
  --       \ (a_M2S, ab_S2M)
  --         -> let
  --              (ab_M2S, (a_S2M, _b_S2M)) = run0 idC ((a_M2S, def), ab_S2M)
  --            in (ab_M2S, a_S2M)

unfstC2 :: Circuit (DF a) (DF a, DF b)
unfstC2 = circuit $ \a -> do
  ab <- idC -< (a, _b)
  ab' <- idC -< ab
  idC -< ab'

-- vecC = Circuit \ (Cons x_M2S (Cons y_M2S Nil), (x_S2M, y_S2M))
--                         -> ((x_M2S, y_M2S), Cons x_S2M (Cons y_S2M (Nil)))
