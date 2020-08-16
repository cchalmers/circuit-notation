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

import Data.Default (def)

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

unsafeC :: Circuit a b
unsafeC = undefined

-- types1 :: Circuit a a
-- types1 = circuit $ \a -> do
--   x :: Int <- unsafeC -< a
--   b <- unsafeC -< x
--   idC -< b

registerC :: a -> Circuit (Signal dom a) (Signal dom a)
registerC a = Circuit $ \(s, ()) -> (a :- s, ())

-- zip2S :: (Signal dom a, Signal dom b) -> Signal dom (a, b)
-- zip2S (a :- as, b :- bs) = (a, b) :- zip2S (as, bs)

-- unzip2S :: Signal dom (a, b) -> (Signal dom a, Signal dom b)
-- unzip2S ((a, b) :- asbs) =
--   let ~(as, bs) = unzip2S asbs
--   in  (a :- as, b :- bs)

-- counter :: Circuit () (Signal dom Int)
-- counter = circuitS do
--   Signal n <- registerC 0 -< Signal n'
--   let n' = n + 1
--   idC -< Signal n

counterExpanded :: Circuit () (Signal dom Int)
counterExpanded =
  let
    circuitLogic =
      \ n ->
        let n' = n + 1
        in  n'
  in Circuit $
      \ ((), ())
        -> let
               (nSig, ()) = runCircuit (registerC 0) (n'Sig, ())

               n'Sig = fmap circuitLogic nSig
           in (nSig, ())

counter2Expanded :: Circuit () (Signal dom (Int, Int))
counter2Expanded =
  let
    circuitLogic =
      \ (n,m) ->
        let n' = n + 1
            m' = m + 1
        in  (n', m')
  in Circuit $
      \ ((), ())
        -> let (nSig, ()) = runCircuit (registerC 0) (n'Sig, ())
               (mSig, ()) = runCircuit (registerC 0) (m'Sig, ())
               (n'Sig, m'Sig) = unbundle (fmap circuitLogic (bundle (nSig, mSig)))
               -- is this version nicer?
               -- (n'Sig, m'Sig) = unbundle (circuitLogic <$> nSig <*> mSig)
           in (bundle (n'Sig, m'Sig), ())

-- writePacketDriver
--   :: Circuit
--      ( DF dom (Unsigned packetSize, BitVector addr, BitVector id)
--      , DF dom (BitVector dat)
--      )
--      ( Axi addr dat id () )
-- writePacketDriver = circuitS
--   \(packetAddr :-> packetAck, writeData :-> writeAck) -> do

--   Signal addr <- registerC 0 -< Signal addr'
--   let addr'
--         | newPacket = packetAddr
--         | otherwise = addr + burstOffset

  

-- counter2 :: Circuit () (Signal dom (Int, Int))
-- counter2 = circuitS do
--   Signal n <- registerC 0 -< Signal n'
--   Signal m <- registerC 8 -< Signal m'
--   let n' = n + 1
--   let m' = m + 1
--   idC -< Signal (n, m)

counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
-- counter3 = let
--   inferenceHelper ::
--     () =>
--     ((Circuit (Signal dom sig_2_1701703739) (Signal dom sig_3_1701701011)
--       -> CircuitT (Signal dom sig_2_1701703739) (Signal dom sig_3_1701701011),
--       Circuit (Signal dom sig_4_1711713739) (Signal dom sig_5_1711711011)
--       -> CircuitT (Signal dom sig_4_1711713739) (Signal dom sig_5_1711711011))
--      -> CircuitT _bsTy (Signal dom sig_1))
--     -> Circuit _bsTy (Signal dom sig_1)
--   inferenceHelper = \ f -> Circuit (f (runCircuit, runCircuit))
--   circuitLogic
--     = \ (n, m)
--         -> let
--              n' = n + 1
--              m' = m + 1
--            in ((n' + m'), n', m')
--   in
--   inferenceHelper
--     \ (run0, run1) (_bs_M2S, _)
--       -> let
--            (hello0, n', m') = unbundle (fmap circuitLogic (bundle (n, m)))
--            _bs_S2M = def
--            (n, _) = run0 (registerC 0) (n', ())
--            (m, _) = run1 (registerC 8) (m', ())
--          in (bundle hello0, _bs_S2M)

counter3 = circuitS \_bs -> do
  Signal n <- registerC 0 -< Signal n'
  Signal m <- registerC 8 -< Signal m'
  let n' = n + 1
      m' = m + 1
  idC -< Signal (n' + m')

-- inout :: Circuit (Signal dom Int) (Signal dom Int)
-- inout = circuitS \(Signal j) -> do
--   Signal j' <- registerC 0 -< Signal j
--   let a = j' + 2
--   idC -< Signal a

-- latest :: Circuit (DF Int) (Signal Int)
-- latest = circuitS $ \(DFM2S v a) -> do
--   l <- registerC 0 -< if v then a else l
--   idC -< l



-- unfstC2 :: Circuit (DF dom a) (DF dom a, DF dom b)
-- unfstC2 = circuit $ \a -> do
--   ab <- idC -< (a, _b)
--   ab' <- idC -< ab
--   idC -< ab'

-- vecC = Circuit \ (Cons x_M2S (Cons y_M2S Nil), (x_S2M, y_S2M))
--                         -> ((x_M2S, y_M2S), Cons x_S2M (Cons y_S2M (Nil)))
