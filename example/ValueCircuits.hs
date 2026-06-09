{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

Examples of value-level circuits (the 'circuitS' keyword). These are
simulated and checked by tests/unittests.hs.
-}

{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
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

-- | Run a circuit whose buses have trivial backwards channels (such as
-- 'Signal' buses, or tuples and 'Vec's of them) by feeding it forward values.
simulateC :: TrivialBwd (Bwd b) => Circuit a b -> Fwd a -> Fwd b
simulateC c aFwd = let (_ :-> bFwd) = runCircuit c (aFwd :-> unitBwd) in bFwd

-- Basic shapes ---------------------------------------------------------

-- | Trivial pass-through: a single value in and a single value out, no
-- feedback. @a@ is the per-cycle 'Int' carried on the bus, not the bus
-- itself; no @bundle@/@unbundle@ is generated for single buses.
plusOne :: Circuit (Signal dom Int) (Signal dom Int)
plusOne = circuitS \(Signal a) -> do
  idC -< Signal (a + 1)

-- | The @Fwd@ keyword can be used interchangeably with @Signal@ to mark the
-- value boundary.
plusOneFwd :: Circuit (Signal dom Int) (Signal dom Int)
plusOneFwd = circuitS \(Fwd a) -> do
  idC -< Fwd (a + 1)

-- | No value inputs at all: the logic is constant.
alwaysFive :: Circuit () (Signal dom Int)
alwaysFive = circuitS do
  idC -< Signal (5 :: Int)

-- | Two value inputs, one value output (a single @bundle@, no @unbundle@).
addC :: Circuit (Signal dom Int, Signal dom Int) (Signal dom Int)
addC = circuitS \(Signal a, Signal b) -> do
  idC -< Signal (a + b)

-- | One value input, two value outputs (a single @unbundle@, no @bundle@).
fanOutC :: Circuit (Signal dom Int) (Signal dom Int, Signal dom Int)
fanOutC = circuitS \(Signal a) -> do
  idC -< (Signal (a + 1), Signal (a * 2))

-- | Values can be matched out of a bus carrying a compound type ...
splitC :: Circuit (Signal dom (Int, Bool)) (Signal dom Int, Signal dom Bool)
splitC = circuitS \(Signal (a, b)) -> do
  idC -< (Signal a, Signal b)

-- | ... and combined back onto one.
joinC :: Circuit (Signal dom Int, Signal dom Bool) (Signal dom (Int, Bool))
joinC = circuitS \(Signal a, Signal b) -> do
  idC -< Signal (a, b)

-- | Ports nest like in ordinary circuit notation.
nestedTupleC :: Circuit ((Signal dom Int, Signal dom Int), Signal dom Int) (Signal dom Int)
nestedTupleC = circuitS \((Signal a, Signal b), Signal c) -> do
  idC -< Signal (a + b * c)

-- | Value boundaries inside 'Vec' buses.
vecInC :: Circuit (Vec 2 (Signal dom Int)) (Signal dom Int)
vecInC = circuitS \[Signal a, Signal b] -> do
  idC -< Signal (a - b)

vecOutC :: Circuit (Signal dom Int) (Vec 2 (Signal dom Int))
vecOutC = circuitS \(Signal a) -> do
  idC -< [Signal (a + 1), Signal (a - 1)]

-- | Ports crossing the value boundary can be given bus-level type
-- annotations like any other port.
annotatedC :: forall dom. Circuit (Signal dom Int) (Signal dom Int)
annotatedC = circuitS \((Signal a) :: Signal dom Int) -> do
  idC -< Signal (a + 1)

-- Feedback -------------------------------------------------------------

-- | A single-register counter with a feedback loop. The register's input
-- @n'@ is defined in terms of its output @n@ by an ordinary recursive @let@;
-- the plugin ties the knot at the signal level.
counter :: Circuit () (Signal dom Int)
counter = circuitS do
  Signal n <- registerC 0 -< Signal n'
  let n' = n + 1
  idC -< Signal n

-- | A Mealy-style accumulator: reads the per-cycle value off the input bus
-- and feeds back state through a register. Written with a @$@ chain.
accum :: Circuit (Signal dom Int) (Signal dom Int)
accum = circuitS $ \(Signal i) -> do
  Signal acc <- registerC 0 -< Signal acc'
  let acc' = acc + i
  idC -< Signal acc'

-- | Two interleaved feedback loops (the canonical example from the design
-- notes). The bus input is ignored.
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
-- buses and a lazy let binding ties the feedback knot. 'SigTag' is 'BusTag'
-- with its bus type pinned to a signal, which keeps inference going where
-- the non-injective 'Fwd' family would otherwise lose it.
counter3Expanded :: Circuit (Signal dom Bool) (Signal dom Int)
counter3Expanded = TagCircuit $ \(_bs_Fwd :-> _) ->
  let
    circuitLogic = \(n, m) ->
      let n' = n + 1
          m' = m + 1
      in  (n', m', n' + m')

    (valOut0, valOut1, valOut2) =
      unbundle (fmap circuitLogic (bundle (valIn0, valIn1)))

    (_ :-> SigTag valIn0) = runTagCircuit (registerC 0) (SigTag valOut0 :-> BusTag unitBwd)
    (_ :-> SigTag valIn1) = runTagCircuit (registerC 8) (SigTag valOut1 :-> BusTag unitBwd)

    _bs_Bwd = BusTag def
  in (_bs_Bwd :-> SigTag valOut2)

-- | Compound state fed back through a /single/ register: a fibonacci
-- machine. The pair is destructured and rebuilt at the value level.
fibC :: Circuit () (Signal dom Int)
fibC = circuitS do
  Signal (a, b) <- registerC (0, 1) -< Signal (b, a + b)
  idC -< Signal a

-- | A chain of registers: a three-deep shift register (no feedback, but a
-- value passes through several binds).
shift3 :: Circuit (Signal dom Int) (Signal dom Int)
shift3 = circuitS \(Signal i) -> do
  Signal a <- registerC 0 -< Signal i
  Signal b <- registerC 0 -< Signal a
  Signal c <- registerC 0 -< Signal b
  idC -< Signal c

-- | Three rotating registers plus the bus input: a four-way bundle on both
-- sides of the logic function.
rotate3 :: Circuit (Signal dom Int) (Signal dom Int)
rotate3 = circuitS \(Signal i) -> do
  Signal a <- registerC 1 -< Signal a'
  Signal b <- registerC 2 -< Signal b'
  Signal c <- registerC 3 -< Signal c'
  let a' = b
      b' = c
      c' = a + i
  idC -< Signal (a + b + c)

-- Mixing value land and bus land ----------------------------------------

-- | Value-level and bus-level ports can be mixed: the second bus is routed
-- through untouched while the first is sampled and modified.
mixedC :: Circuit (Signal dom Int, Signal dom Int) (Signal dom Int, Signal dom Int)
mixedC = circuitS \(Signal a, b) -> do
  idC -< (Signal (a + 1), b)

-- | As 'mixedC' but with a 'DF' bus (whose backwards channel is not
-- trivial) routed through.
mixedDfC :: Circuit (Signal dom Int, DF dom Bool) (Signal dom Int, DF dom Bool)
mixedDfC = circuitS \(Signal a, df) -> do
  idC -< (Signal (a + 1), df)

-- | A bus created from a value can be multicast like any other bus.
multicastC :: Circuit (Signal dom Int) (Signal dom Int, Signal dom Int)
multicastC = circuitS \(Signal a) -> do
  b <- idC -< Signal (a + 1)
  idC -< (b, b)

-- | Without any value-level (@Signal@/@Fwd@) markers, @circuitS@ behaves
-- exactly like @circuit@.
passthrough :: Circuit (Signal dom Int) (Signal dom Int)
passthrough = circuitS \a -> a

-- Nesting ---------------------------------------------------------------

-- | A @circuitS@ used as a sub-circuit inside an ordinary @circuit@.
nestedSInCircuit :: Circuit (Signal dom Int) (Signal dom Int)
nestedSInCircuit = circuit $ \a -> do
  b <- (circuitS \(Signal x) -> do idC -< Signal (x * 2)) -< a
  idC -< b

-- | An ordinary @circuit@ used as a sub-circuit inside a @circuitS@.
nestedCircuitInS :: Circuit (Signal dom Int) (Signal dom Int)
nestedCircuitInS = circuitS \(Signal x) -> do
  Signal y <- (circuit \b -> b) -< Signal (x + 1)
  idC -< Signal (y * 3)

-- | A @circuitS@ inside another @circuitS@.
nestedSInS :: Circuit (Signal dom Int) (Signal dom Int)
nestedSInS = circuitS \(Signal x) -> do
  Signal y <- (circuitS \(Signal a) -> do idC -< Signal (a + 1)) -< Signal x
  idC -< Signal (y * 2)
