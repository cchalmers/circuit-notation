{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

Examples of value-level circuits (the 'circuitS' keyword).
-}

{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}
{-# OPTIONS -Wall #-}

module ValueCircuits where

import           Circuit

import           Clash.Prelude
import           Clash.Signal.Internal (Signal ((:-)))

-- | A register as a circuit: the output bus carries the input bus delayed by
-- one cycle, starting with the given value.
registerC :: a -> Circuit (Signal dom a) (Signal dom a)
registerC a = Circuit $ \(s :-> ()) -> (() :-> (a :- s))

-- | Run a circuit whose buses are plain signals (and so have trivial
-- backwards channels).
simulateSigCircuit :: Circuit (Signal dom a) (Signal dom b) -> Signal dom a -> Signal dom b
simulateSigCircuit c as = let (() :-> bs) = runCircuit c (as :-> ()) in bs

-- | Like 'simulateSigCircuit' for a circuit with no input.
simulateUnitCircuit :: Circuit () (Signal dom b) -> Signal dom b
simulateUnitCircuit c = let (() :-> bs) = runCircuit c (() :-> ()) in bs

-- | Trivial pass-through: a single value in and a single value out, no
-- feedback. @a@ is the per-cycle 'Int' carried on the bus, not the bus
-- itself; no @bundle@/@unbundle@ is generated for single buses.
--
-- >>> sampleN @System 5 (simulateSigCircuit plusOne (fromList [0..]))
-- [1,2,3,4,5]
plusOne :: Circuit (Signal dom Int) (Signal dom Int)
plusOne = circuitS \(Signal a) -> do
  idC -< Signal (a + 1)

-- | A single-register counter with a feedback loop. The register's input
-- @n'@ is defined in terms of its output @n@ by an ordinary recursive @let@;
-- the plugin ties the knot at the signal level.
--
-- >>> sampleN @System 5 (simulateUnitCircuit counter)
-- [0,1,2,3,4]
counter :: Circuit () (Signal dom Int)
counter = circuitS do
  Signal n <- registerC 0 -< Signal n'
  let n' = n + 1
  idC -< Signal n

-- | A Mealy-style accumulator: reads the per-cycle value off the input bus
-- and feeds back state through a register. Written with a @$@ chain.
--
-- >>> sampleN @System 5 (simulateSigCircuit accum (fromList [1..]))
-- [1,3,6,10,15]
accum :: Circuit (Signal dom Int) (Signal dom Int)
accum = circuitS $ \(Signal i) -> do
  Signal acc <- registerC 0 -< Signal acc'
  let acc' = acc + i
  idC -< Signal acc'

-- | Two interleaved feedback loops (the canonical example from the design
-- notes). The bus input is ignored.
--
-- >>> sampleN @System 5 (simulateSigCircuit counter3 (pure False))
-- [10,12,14,16,18]
counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
counter3 = circuitS \_bs -> do
  Signal n <- registerC 0 -< Signal n'
  Signal m <- registerC 8 -< Signal m'
  let n' = n + 1
      m' = m + 1
  idC -< Signal (n' + m')

-- | What 'counter3' expands to (modulo generated names). The value-level
-- bindings are collected into one pure function, @circuitLogic@, which is
-- lifted to the signal level with 'fmap'; 'bundle'/'unbundle' group the
-- buses and a lazy let binding ties the feedback knot.
counter3Expanded :: Circuit (Signal dom Bool) (Signal dom Int)
counter3Expanded = TagCircuit $ \(_bs_Fwd :-> _) ->
  let
    circuitLogic = \(n, m) ->
      let n' = n + 1
          m' = m + 1
      in  (n', m', n' + m')

    (valOut0, valOut1, valOut2) =
      unbundle (fmap circuitLogic (bundle (valIn0, valIn1)))

    (_ :-> BusTag valIn0) = runTagCircuit (registerC 0) (BusTag valOut0 :-> BusTag unitBwd)
    (_ :-> BusTag valIn1) = runTagCircuit (registerC 8) (BusTag valOut1 :-> BusTag unitBwd)

    _bs_Bwd = BusTag def
  in (_bs_Bwd :-> BusTag valOut2)

-- | Value-level and bus-level ports can be mixed: the 'DF' bus is routed
-- through untouched while the signal is sampled and modified.
mixed :: Circuit (Signal dom Int, DF dom Bool) (Signal dom Int, DF dom Bool)
mixed = circuitS \(Signal a, df) -> do
  idC -< (Signal (a + 1), df)

-- | Without any value-level (@Signal@/@Fwd@) markers, @circuitS@ behaves
-- exactly like @circuit@.
passthrough :: Circuit (Signal dom Int) (Signal dom Int)
passthrough = circuitS \a -> a
