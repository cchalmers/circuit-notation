# circuit-notation

This is a plugin for manipulating circuits in clash with arrow notation. See example/Example.hs for
example usage. Also see [clash-protocols](https://github.com/clash-lang/clash-protocols#).

## Value-level circuits (`circuitV`)

The `circuitV` keyword describes a circuit's logic over the *values sampled
each clock cycle* instead of over whole buses. The boundary between bus land
and value land is marked with `Signal` (or `Fwd`):

- `Signal n <- … -< …` binds `n` to the per-cycle value carried on that bus.
- `… -< Signal e` injects the per-cycle value `e` back onto a bus.

Everything in between — the `let` bindings of the do block — is ordinary pure
Haskell, and feedback loops are written as ordinary recursive `let`s:

```haskell
counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
counter3 = circuitV \_bs -> do
  Signal n <- registerC 0 -< Signal n'      -- n  :: Int (this cycle's value)
  Signal m <- registerC 8 -< Signal m'      -- m  :: Int
  let n' = n + 1                            -- pure, value-level
      m' = m + 1
  idC -< Signal (n' + m')
```

The plugin collects the value-level bindings into pure functions, lifts them
to the signal level with `fmap` (using `bundle`/`unbundle` to group the
buses), and ties feedback knots with lazy let bindings. See
example/ValueCircuits.hs for more examples and the expansion of `counter3`.

A single `circuitV` block can span several clock domains: the value-level
bindings are split into groups connected by shared variables, and each group
is lifted independently, so only buses whose values actually meet must share
a clock domain. Two independent counters on two different domains can live
in one block; making their values meet (e.g. `Signal (n + m)`) is an
unsynchronized clock domain crossing and is rejected by the type checker
(cross between domains with explicit bus-level synchronizer circuits
instead).

Notes:

- Pattern match down to *exactly* the `Signal` layer, no shallower; the
  plugin cannot (yet) know which types contain signals, so the boundary has
  to be explicit. Marking a bus that is not a `Signal` (e.g. a `Vec` of
  signals) is a type error on the offending statement.
- In a `circuitV` block, `let` statements that use value-level variables
  form the bodies of the generated logic functions; `let`s that don't touch
  value land (e.g. a let-bound sub-circuit) stay at the bus level and can be
  used with `-<`.
- The grouping is syntactic and conservative: shadowing a value-level name
  inside a `let` can merge groups that wouldn't strictly need to share a
  domain (never the other way around).
