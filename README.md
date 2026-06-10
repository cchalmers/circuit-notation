# circuit-notation

This is a plugin for manipulating circuits in clash with arrow notation. See example/Example.hs for
example usage. Also see [clash-protocols](https://github.com/clash-lang/clash-protocols#).

## Value-level ports (`SignalV` / `FwdV`)

The `SignalV` and `FwdV` markers describe a circuit's logic over the *values
sampled each clock cycle* instead of over whole buses, right inside an
ordinary `circuit` block:

- `SignalV n <- … -< …` binds `n` to the per-cycle value carried on that bus.
- `… -< SignalV e` injects the per-cycle value `e` back onto a bus.

(The bus-level `Signal`/`Fwd` markers, which bind the raw forward channel,
keep their existing meaning; the two levels can be mixed freely in one
block.)

The two value markers differ in what buses they accept:

- `SignalV x` asserts the bus *is* a `Signal dom a`; it pins the bus type
  and so gives the best type inference (it works against fully generic
  sub-circuits like `idC`).
- `FwdV x` samples (or drives) the forward channel of *any* signal-like
  bus — any `SignalBus` instance: `Signal`s, `Vec`s and tuples of
  signal-like buses (sampled as `Vec`s/tuples of values), and custom buses
  given a one-line instance. In exchange, the bus type must be determined by
  context (the circuit's signature or a concretely typed sub-circuit), and
  pattern uses need a trivial backwards channel (`TrivialBwd (Bwd t)`).

Everything in between — the `let` bindings of the do block — is ordinary pure
Haskell, and feedback loops are written as ordinary recursive `let`s:

```haskell
counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
counter3 = circuit \_bs -> do
  SignalV n <- registerC 0 -< SignalV n'    -- n  :: Int (this cycle's value)
  SignalV m <- registerC 8 -< SignalV m'    -- m  :: Int
  let n' = n + 1                            -- pure, value-level
      m' = m + 1
  idC -< SignalV (n' + m')
```

The plugin collects the value-level bindings into pure functions, lifts them
to the signal level with `fmap` (using `bundle`/`unbundle` to group the
buses), and ties feedback knots with lazy let bindings. See
example/ValueCircuits.hs for more examples and the expansion of `counter3`.

A single block can span several clock domains: the value-level bindings are
split into groups connected by shared variables, and each group is lifted
independently, so only buses whose values actually meet must share a clock
domain. Two independent counters on two different domains can live in one
block; making their values meet (e.g. `SignalV (n + m)`) is an
unsynchronized clock domain crossing and is rejected by the type checker
(cross between domains with explicit bus-level synchronizer circuits
instead).

Notes:

- Pattern match down to *exactly* the signal layer, no shallower; the
  plugin cannot (yet) know which types contain signals, so the boundary has
  to be explicit. Marking a bus with `SignalV` when it is not a `Signal`
  (e.g. a `Vec` of signals) is a type error on the offending statement —
  use `FwdV` to sample such buses whole.
- `let` statements that use value-level variables form the bodies of the
  generated logic functions; `let`s that don't touch value land (e.g. a
  let-bound sub-circuit) stay at the bus level and can be used with `-<`.
- The grouping is syntactic and conservative: shadowing a value-level name
  inside a `let` can merge groups that wouldn't strictly need to share a
  domain (never the other way around).
