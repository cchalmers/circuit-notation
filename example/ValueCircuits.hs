{-
 ██████╗██╗██████╗  ██████╗██╗   ██╗██╗████████╗███████╗
██╔════╝██║██╔══██╗██╔════╝██║   ██║██║╚══██╔══╝██╔════╝
██║     ██║██████╔╝██║     ██║   ██║██║   ██║   ███████╗
██║     ██║██╔══██╗██║     ██║   ██║██║   ██║   ╚════██║
╚██████╗██║██║  ██║╚██████╗╚██████╔╝██║   ██║   ███████║
 ╚═════╝╚═╝╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝   ╚═╝   ╚══════╝
  (C) 2020, Christopher Chalmers

Examples of value-level ports (the 'SignalV' and 'FwdV' markers) in circuit
blocks. These are simulated and checked by tests/unittests.hs.
-}

{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

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
plusOne = circuit \(SignalV a) -> do
  idC -< SignalV (a + 1)

-- | The same as 'plusOne' without a do block: a bare expression body.
plusOneBare :: Circuit (Signal dom Int) (Signal dom Int)
plusOneBare = circuit \(SignalV a) -> SignalV (a + 1)

-- | The @FwdV@ marker also marks the value boundary, but works on /any/
-- signal-like bus (any 'SignalBus' instance) rather than only literal
-- 'Signal's. The trade-off: the bus type must be determined by context
-- (here, the signature).
plusOneFwd :: Circuit (Signal dom Int) (Signal dom Int)
plusOneFwd = circuit \(FwdV a) -> do
  idC -< FwdV (a + 1)

-- | A whole 'Vec' of signal buses sampled as a single @Vec n Int@ value per
-- cycle (via the 'SignalBus' instance for 'Vec').
vecSampleC :: Circuit (Vec 2 (Signal dom Int)) (Signal dom Int)
vecSampleC = circuit \(FwdV v) -> do
  idC -< SignalV (sum v)

-- | ... and emitted back as one: a @Vec 2 Int@ value drives both buses.
vecEmitC :: Circuit (Signal dom Int) (Vec 2 (Signal dom Int))
vecEmitC = circuit \(SignalV a) -> do
  idC -< FwdV (a :> (a + 1) :> Nil)

-- | @SignalV@ and @FwdV@ markers can meet in the same logic group.
mixedMarkersC :: Circuit (Signal dom Int, Vec 2 (Signal dom Int)) (Signal dom Int)
mixedMarkersC = circuit \(SignalV a, FwdV v) -> do
  idC -< SignalV (a + sum v)

-- | A custom signal-like bus: a stream of optionally-valid values with no
-- backpressure. The 'SignalBus' instance is all that's needed for @FwdV@
-- markers to sample and drive it in circuit blocks.
-- The explicit result kind matters: without it, PolyKinds (on by default in
-- GHC2021+) would infer a poly-kinded @a@ for this empty data declaration.
data VStream (dom :: Domain) (a :: Type)
type instance Fwd (VStream dom a) = Signal dom (Maybe a)
type instance Bwd (VStream dom a) = ()

instance SignalBus (VStream dom a) where
  type BusDom (VStream dom a) = dom
  type SampleOf (VStream dom a) = Maybe a
  sigFromBus = unBusTag
  sigToBus = BusTag

vstreamC :: Circuit (VStream dom Int) (VStream dom Int)
vstreamC = circuit \(FwdV m) -> do
  idC -< FwdV (fmap (+ 1) m)

-- | No value inputs at all: the logic is constant.
alwaysFive :: Circuit () (Signal dom Int)
alwaysFive = circuit do
  idC -< SignalV (5 :: Int)

-- | Two value inputs, one value output (a single @bundle@, no @unbundle@).
addC :: Circuit (Signal dom Int, Signal dom Int) (Signal dom Int)
addC = circuit \(SignalV a, SignalV b) -> do
  idC -< SignalV (a + b)

-- | One value input, two value outputs (a single @unbundle@, no @bundle@).
fanOutC :: Circuit (Signal dom Int) (Signal dom Int, Signal dom Int)
fanOutC = circuit \(SignalV a) -> do
  idC -< (SignalV (a + 1), SignalV (a * 2))

-- | Values can be matched out of a bus carrying a compound type ...
splitC :: Circuit (Signal dom (Int, Bool)) (Signal dom Int, Signal dom Bool)
splitC = circuit \(SignalV (a, b)) -> do
  idC -< (SignalV a, SignalV b)

-- | ... and combined back onto one.
joinC :: Circuit (Signal dom Int, Signal dom Bool) (Signal dom (Int, Bool))
joinC = circuit \(SignalV a, SignalV b) -> do
  idC -< SignalV (a, b)

-- | Ports nest like in ordinary circuit notation.
nestedTupleC :: Circuit ((Signal dom Int, Signal dom Int), Signal dom Int) (Signal dom Int)
nestedTupleC = circuit \((SignalV a, SignalV b), SignalV c) -> do
  idC -< SignalV (a + b * c)

-- | Value boundaries inside 'Vec' buses.
vecInC :: Circuit (Vec 2 (Signal dom Int)) (Signal dom Int)
vecInC = circuit \[SignalV a, SignalV b] -> do
  idC -< SignalV (a - b)

vecOutC :: Circuit (Signal dom Int) (Vec 2 (Signal dom Int))
vecOutC = circuit \(SignalV a) -> do
  idC -< [SignalV (a + 1), SignalV (a - 1)]

-- | Ports crossing the value boundary can be given bus-level type
-- annotations like any other port.
annotatedC :: forall dom. Circuit (Signal dom Int) (Signal dom Int)
annotatedC = circuit \((SignalV a) :: Signal dom Int) -> do
  idC -< SignalV (a + 1)

-- Feedback -------------------------------------------------------------

-- | A single-register counter with a feedback loop. The register's input
-- @n'@ is defined in terms of its output @n@ by an ordinary recursive @let@;
-- the plugin ties the knot at the signal level.
counter :: Circuit () (Signal dom Int)
counter = circuit do
  SignalV n <- registerC 0 -< SignalV n'
  let n' = n + 1
  idC -< SignalV n

-- | A Mealy-style accumulator: reads the per-cycle value off the input bus
-- and feeds back state through a register. Written with a @$@ chain.
accum :: Circuit (Signal dom Int) (Signal dom Int)
accum = circuit $ \(SignalV i) -> do
  SignalV acc <- registerC 0 -< SignalV acc'
  let acc' = acc + i
  idC -< SignalV acc'

-- | Two interleaved feedback loops (the canonical example from the design
-- notes). The bus input is ignored.
counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
counter3 = circuit \_bs -> do
  SignalV n <- registerC 0 -< SignalV n'
  SignalV m <- registerC 8 -< SignalV m'
  let n' = n + 1
      m' = m + 1
  idC -< SignalV (n' + m')

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
fibC = circuit do
  SignalV (a, b) <- registerC (0, 1) -< SignalV (b, a + b)
  idC -< SignalV a

-- | A chain of registers: a three-deep shift register (no feedback, but a
-- value passes through several binds).
shift3 :: Circuit (Signal dom Int) (Signal dom Int)
shift3 = circuit \(SignalV i) -> do
  SignalV a <- registerC 0 -< SignalV i
  SignalV b <- registerC 0 -< SignalV a
  SignalV c <- registerC 0 -< SignalV b
  idC -< SignalV c

-- | Three rotating registers plus the bus input: a four-way bundle on both
-- sides of the logic function.
rotate3 :: Circuit (Signal dom Int) (Signal dom Int)
rotate3 = circuit \(SignalV i) -> do
  SignalV a <- registerC 1 -< SignalV a'
  SignalV b <- registerC 2 -< SignalV b'
  SignalV c <- registerC 3 -< SignalV c'
  let a' = b
      b' = c
      c' = a + i
  idC -< SignalV (a + b + c)

-- Mixing value land and bus land ----------------------------------------

-- | Value-level and bus-level ports can be mixed: the second bus is routed
-- through untouched while the first is sampled and modified.
mixedC :: Circuit (Signal dom Int, Signal dom Int) (Signal dom Int, Signal dom Int)
mixedC = circuit \(SignalV a, b) -> do
  idC -< (SignalV (a + 1), b)

-- | As 'mixedC' but with a 'DF' bus (whose backwards channel is not
-- trivial) routed through.
mixedDfC :: Circuit (Signal dom Int, DF dom Bool) (Signal dom Int, DF dom Bool)
mixedDfC = circuit \(SignalV a, df) -> do
  idC -< (SignalV (a + 1), df)

-- | Bus-level markers (@Fwd@/@Signal@, which bind the raw forward channel)
-- and value-level markers (@FwdV@/@SignalV@) can be used side by side in
-- one block: here the 'Vec' bus is rearranged at the bus level while the
-- signal is sampled.
mixedLevelsC :: Circuit (Vec 2 (Signal dom Int), Signal dom Int) (Vec 2 (Signal dom Int), Signal dom Int)
mixedLevelsC = circuit \(Fwd v, SignalV a) -> do
  idC -< (Fwd (rotateLeftS v d1), SignalV (a + 1))

-- | A bus created from a value can be multicast like any other bus.
multicastC :: Circuit (Signal dom Int) (Signal dom Int, Signal dom Int)
multicastC = circuit \(SignalV a) -> do
  b <- idC -< SignalV (a + 1)
  idC -< (b, b)

-- | Without any value-level markers this is just ordinary circuit notation.
passthrough :: Circuit (Signal dom Int) (Signal dom Int)
passthrough = circuit \a -> a

-- Delayed signals --------------------------------------------------------
--
-- @DSignalV@ marks the value boundary on 'DSignal' buses. The generated
-- @DSigTag@ pins the bus type /including the delay index/, and a delayed
-- group's bundle unifies the delays of everything in it: all values that
-- meet must come from (and go to) buses at the same pipeline depth. The
-- lifted logic is combinational, so a group's outputs are produced at the
-- same delay its inputs are sampled at. Groups at different delays can
-- coexist in one block.

-- | A delayed register: the output is one cycle (and one delay index)
-- behind the input.
dregisterC :: a -> Circuit (DSignal dom d a) (DSignal dom (d + 1) a)
dregisterC a = Circuit $ \(s :-> ()) -> (() :-> unsafeFromSignal (a :- toSignal s))

-- | Delay-polymorphic pass-through: works at any pipeline depth, and pins
-- input and output to the /same/ depth.
dplusOne :: Circuit (DSignal dom d Int) (DSignal dom d Int)
dplusOne = circuit \(DSignalV a) -> do
  idC -< DSignalV (a + 1)

-- | Two delayed values meeting in one group: their buses must agree on the
-- delay (and domain), which the signature expresses with a single @d@.
daddC :: Circuit (DSignal dom d Int, DSignal dom d Int) (DSignal dom d Int)
daddC = circuit \(DSignalV a, DSignalV b) -> do
  idC -< DSignalV (a + b)

-- | A two-stage pipeline: the @i@ group sits at delay @d@ and the @a@ group
-- at delay @d + 1@ -- two value groups at different pipeline depths in one
-- block, linked by the delayed register at the bus level.
dpipeC :: Circuit (DSignal dom d Int) (DSignal dom (d + 1) Int)
dpipeC = circuit \(DSignalV i) -> do
  DSignalV a <- dregisterC 0 -< DSignalV (i + 1)
  idC -< DSignalV (a * 2)

-- Multiple clock domains -------------------------------------------------
--
-- The plugin splits the value-level logic into groups connected by shared
-- variables and lifts each group with its own fmap/bundle/unbundle, so only
-- buses whose values actually meet must share a clock domain. Sharing a
-- value across domains is an (unsynchronized) clock domain crossing and is
-- rejected by the type checker.

-- | Two completely independent counters in one block, on two /different/
-- clock domains: nothing forces @domA@ and @domB@ together.
dualCounter :: Circuit (Signal domA Bool, Signal domB Bool) (Signal domA Int, Signal domB Int)
dualCounter = circuit \(_ea, _eb) -> do
  SignalV n <- registerC 0 -< SignalV n'
  SignalV m <- registerC 8 -< SignalV m'
  let n' = n + 1
      m' = m + 1
  idC -< (SignalV n', SignalV m')

-- | Two independent accumulators, each reading values off its own input
-- bus, on different clock domains.
dualAccum :: Circuit (Signal domA Int, Signal domB Int) (Signal domA Int, Signal domB Int)
dualAccum = circuit \(SignalV i, SignalV j) -> do
  SignalV a <- registerC 0 -< SignalV (a + i)
  SignalV b <- registerC 0 -< SignalV (b + j)
  idC -< (SignalV a, SignalV b)

-- | Lets that don't touch any value-level variable stay at the bus level,
-- so sub-circuits can be bound in a let and used with @-<@.
busLevelLet :: Circuit (Signal dom Int) (Signal dom Int)
busLevelLet = circuit \(SignalV x) -> do
  let inc = plusOne
  SignalV y <- inc -< SignalV (x + 1)
  idC -< SignalV (y * 2)

-- Nesting ---------------------------------------------------------------

-- | A value-level circuit used as a sub-circuit inside a bus-level one.
nestedSInCircuit :: Circuit (Signal dom Int) (Signal dom Int)
nestedSInCircuit = circuit $ \a -> do
  b <- (circuit \(SignalV x) -> do idC -< SignalV (x * 2)) -< a
  idC -< b

-- | A bus-level circuit used as a sub-circuit inside a value-level one.
nestedCircuitInS :: Circuit (Signal dom Int) (Signal dom Int)
nestedCircuitInS = circuit \(SignalV x) -> do
  SignalV y <- (circuit \b -> b) -< SignalV (x + 1)
  idC -< SignalV (y * 3)

-- | A value-level circuit inside another value-level circuit.
nestedSInS :: Circuit (Signal dom Int) (Signal dom Int)
nestedSInS = circuit \(SignalV x) -> do
  SignalV y <- (circuit \(SignalV a) -> do idC -< SignalV (a + 1)) -< SignalV x
  idC -< SignalV (y * 2)
