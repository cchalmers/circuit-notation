{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

Examples of value-level circuits (the 'circuitV' keyword). These are
simulated and checked by tests/unittests.hs.
-}

{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}

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
plusOne = circuitV \(Signal a) -> do
  idC -< Signal (a + 1)

-- | The same as 'plusOne' without a do block: a bare expression body.
plusOneBare :: Circuit (Signal dom Int) (Signal dom Int)
plusOneBare = circuitV \(Signal a) -> Signal (a + 1)

-- | The @Fwd@ keyword also marks the value boundary, but works on /any/
-- signal-like bus (any 'SignalBus' instance) rather than only literal
-- 'Signal's. The trade-off: the bus type must be determined by context
-- (here, the signature).
plusOneFwd :: Circuit (Signal dom Int) (Signal dom Int)
plusOneFwd = circuitV \(Fwd a) -> do
  idC -< Fwd (a + 1)

-- | A whole 'Vec' of signal buses sampled as a single @Vec n Int@ value per
-- cycle (via the 'SignalBus' instance for 'Vec').
vecSampleC :: Circuit (Vec 2 (Signal dom Int)) (Signal dom Int)
vecSampleC = circuitV \(Fwd v) -> do
  idC -< Signal (sum v)

-- | ... and emitted back as one: a @Vec 2 Int@ value drives both buses.
vecEmitC :: Circuit (Signal dom Int) (Vec 2 (Signal dom Int))
vecEmitC = circuitV \(Signal a) -> do
  idC -< Fwd (a :> (a + 1) :> Nil)

-- | @Signal@ and @Fwd@ markers can meet in the same logic group.
mixedMarkersC :: Circuit (Signal dom Int, Vec 2 (Signal dom Int)) (Signal dom Int)
mixedMarkersC = circuitV \(Signal a, Fwd v) -> do
  idC -< Signal (a + sum v)

-- | A custom signal-like bus: a stream of optionally-valid values with no
-- backpressure. The 'SignalBus' instance is all that's needed for @Fwd@
-- markers to sample and drive it in @circuitV@ blocks.
data VStream (dom :: Domain) a
type instance Fwd (VStream dom a) = Signal dom (Maybe a)
type instance Bwd (VStream dom a) = ()

instance SignalBus (VStream dom a) where
  type BusDom (VStream dom a) = dom
  type SampleOf (VStream dom a) = Maybe a
  sigFromBus = unBusTag
  sigToBus = BusTag

vstreamC :: Circuit (VStream dom Int) (VStream dom Int)
vstreamC = circuitV \(Fwd m) -> do
  idC -< Fwd (fmap (+ 1) m)

-- | No value inputs at all: the logic is constant.
alwaysFive :: Circuit () (Signal dom Int)
alwaysFive = circuitV do
  idC -< Signal (5 :: Int)

-- | Two value inputs, one value output (a single @bundle@, no @unbundle@).
addC :: Circuit (Signal dom Int, Signal dom Int) (Signal dom Int)
addC = circuitV \(Signal a, Signal b) -> do
  idC -< Signal (a + b)

-- | One value input, two value outputs (a single @unbundle@, no @bundle@).
fanOutC :: Circuit (Signal dom Int) (Signal dom Int, Signal dom Int)
fanOutC = circuitV \(Signal a) -> do
  idC -< (Signal (a + 1), Signal (a * 2))

-- | Values can be matched out of a bus carrying a compound type ...
splitC :: Circuit (Signal dom (Int, Bool)) (Signal dom Int, Signal dom Bool)
splitC = circuitV \(Signal (a, b)) -> do
  idC -< (Signal a, Signal b)

-- | ... and combined back onto one.
joinC :: Circuit (Signal dom Int, Signal dom Bool) (Signal dom (Int, Bool))
joinC = circuitV \(Signal a, Signal b) -> do
  idC -< Signal (a, b)

-- | Ports nest like in ordinary circuit notation.
nestedTupleC :: Circuit ((Signal dom Int, Signal dom Int), Signal dom Int) (Signal dom Int)
nestedTupleC = circuitV \((Signal a, Signal b), Signal c) -> do
  idC -< Signal (a + b * c)

-- | Value boundaries inside 'Vec' buses.
vecInC :: Circuit (Vec 2 (Signal dom Int)) (Signal dom Int)
vecInC = circuitV \[Signal a, Signal b] -> do
  idC -< Signal (a - b)

vecOutC :: Circuit (Signal dom Int) (Vec 2 (Signal dom Int))
vecOutC = circuitV \(Signal a) -> do
  idC -< [Signal (a + 1), Signal (a - 1)]

-- | Ports crossing the value boundary can be given bus-level type
-- annotations like any other port.
annotatedC :: forall dom. Circuit (Signal dom Int) (Signal dom Int)
annotatedC = circuitV \((Signal a) :: Signal dom Int) -> do
  idC -< Signal (a + 1)

-- Feedback -------------------------------------------------------------

-- | A single-register counter with a feedback loop. The register's input
-- @n'@ is defined in terms of its output @n@ by an ordinary recursive @let@;
-- the plugin ties the knot at the signal level.
counter :: Circuit () (Signal dom Int)
counter = circuitV do
  Signal n <- registerC 0 -< Signal n'
  let n' = n + 1
  idC -< Signal n

-- | A Mealy-style accumulator: reads the per-cycle value off the input bus
-- and feeds back state through a register. Written with a @$@ chain.
accum :: Circuit (Signal dom Int) (Signal dom Int)
accum = circuitV $ \(Signal i) -> do
  Signal acc <- registerC 0 -< Signal acc'
  let acc' = acc + i
  idC -< Signal acc'

-- | Two interleaved feedback loops (the canonical example from the design
-- notes). The bus input is ignored.
counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
counter3 = circuitV \_bs -> do
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
fibC = circuitV do
  Signal (a, b) <- registerC (0, 1) -< Signal (b, a + b)
  idC -< Signal a

-- | A chain of registers: a three-deep shift register (no feedback, but a
-- value passes through several binds).
shift3 :: Circuit (Signal dom Int) (Signal dom Int)
shift3 = circuitV \(Signal i) -> do
  Signal a <- registerC 0 -< Signal i
  Signal b <- registerC 0 -< Signal a
  Signal c <- registerC 0 -< Signal b
  idC -< Signal c

-- | Three rotating registers plus the bus input: a four-way bundle on both
-- sides of the logic function.
rotate3 :: Circuit (Signal dom Int) (Signal dom Int)
rotate3 = circuitV \(Signal i) -> do
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
mixedC = circuitV \(Signal a, b) -> do
  idC -< (Signal (a + 1), b)

-- | As 'mixedC' but with a 'DF' bus (whose backwards channel is not
-- trivial) routed through.
mixedDfC :: Circuit (Signal dom Int, DF dom Bool) (Signal dom Int, DF dom Bool)
mixedDfC = circuitV \(Signal a, df) -> do
  idC -< (Signal (a + 1), df)

-- | A bus created from a value can be multicast like any other bus.
multicastC :: Circuit (Signal dom Int) (Signal dom Int, Signal dom Int)
multicastC = circuitV \(Signal a) -> do
  b <- idC -< Signal (a + 1)
  idC -< (b, b)

-- | Without any value-level (@Signal@/@Fwd@) markers, @circuitV@ behaves
-- exactly like @circuit@.
passthrough :: Circuit (Signal dom Int) (Signal dom Int)
passthrough = circuitV \a -> a

-- Multiple clock domains -------------------------------------------------
--
-- The plugin splits the value-level logic into groups connected by shared
-- variables and lifts each group with its own fmap/bundle/unbundle, so only
-- buses whose values actually meet must share a clock domain. Sharing a
-- value across domains is an (unsynchronized) clock domain crossing and is
-- rejected by the type checker.

-- | Two completely independent counters in one @circuitV@ block, on two
-- /different/ clock domains: nothing forces @domA@ and @domB@ together.
dualCounter :: Circuit (Signal domA Bool, Signal domB Bool) (Signal domA Int, Signal domB Int)
dualCounter = circuitV \(_ea, _eb) -> do
  Signal n <- registerC 0 -< Signal n'
  Signal m <- registerC 8 -< Signal m'
  let n' = n + 1
      m' = m + 1
  idC -< (Signal n', Signal m')

-- | Two independent accumulators, each reading values off its own input
-- bus, on different clock domains.
dualAccum :: Circuit (Signal domA Int, Signal domB Int) (Signal domA Int, Signal domB Int)
dualAccum = circuitV \(Signal i, Signal j) -> do
  Signal a <- registerC 0 -< Signal (a + i)
  Signal b <- registerC 0 -< Signal (b + j)
  idC -< (Signal a, Signal b)

-- | Lets that don't touch any value-level variable stay at the bus level,
-- so sub-circuits can be bound in a let and used with @-<@.
busLevelLet :: Circuit (Signal dom Int) (Signal dom Int)
busLevelLet = circuitV \(Signal x) -> do
  let inc = plusOne
  Signal y <- inc -< Signal (x + 1)
  idC -< Signal (y * 2)

-- Nesting ---------------------------------------------------------------

-- | A @circuitV@ used as a sub-circuit inside an ordinary @circuit@.
nestedSInCircuit :: Circuit (Signal dom Int) (Signal dom Int)
nestedSInCircuit = circuit $ \a -> do
  b <- (circuitV \(Signal x) -> do idC -< Signal (x * 2)) -< a
  idC -< b

-- | An ordinary @circuit@ used as a sub-circuit inside a @circuitV@.
nestedCircuitInS :: Circuit (Signal dom Int) (Signal dom Int)
nestedCircuitInS = circuitV \(Signal x) -> do
  Signal y <- (circuit \b -> b) -< Signal (x + 1)
  idC -< Signal (y * 3)

-- | A @circuitV@ inside another @circuitV@.
nestedSInS :: Circuit (Signal dom Int) (Signal dom Int)
nestedSInS = circuitV \(Signal x) -> do
  Signal y <- (circuitV \(Signal a) -> do idC -< Signal (a + 1)) -< Signal x
  idC -< Signal (y * 2)
