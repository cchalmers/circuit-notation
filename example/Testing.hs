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
-- {-# LANGUAGE ScopedTypeVariables  #-}

{-# OPTIONS -fplugin=CircuitNotation #-}
{-# OPTIONS -Wno-unused-local-binds #-}
{-# OPTIONS -Wno-missing-signatures #-}

module Example where

import           Circuit

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

fstC :: Circuit (Signal a, Signal b) (Signal a)
fstC = circuit $ \(a, _b) -> a

-- swapC :: Circuit (a,b) (b,a)
-- swapC = circuit $ \(a,b) -> (b,a)

vecC :: Circuit (Vec 2 a) (a, a)
-- vecC = circuit \[x,y] -> (x,y)
vecC = Circuit \ (Cons x_M2S (Cons y_M2S Nil), (x_S2M, y_S2M))
                        -> ((x_M2S, y_M2S), Cons x_S2M (Cons y_S2M (Nil)))
