# circuit-notation

This is a plugin for manipulating circuits in clash with arrow notation. See example/Example.hs for
example usage. Also see [clash-protocols](https://github.com/clash-lang/clash-protocols#).

## Value-level circuits (`circuitS`)

The `circuitS` keyword describes a circuit's logic over the *values sampled
each clock cycle* instead of over whole buses. The boundary between bus land
and value land is marked with `Signal` (or `Fwd`):

- `Signal n <- … -< …` binds `n` to the per-cycle value carried on that bus.
- `… -< Signal e` injects the per-cycle value `e` back onto a bus.

Everything in between — the `let` bindings of the do block — is ordinary pure
Haskell, and feedback loops are written as ordinary recursive `let`s:

```haskell
counter3 :: Circuit (Signal dom Bool) (Signal dom Int)
counter3 = circuitS \_bs -> do
  Signal n <- registerC 0 -< Signal n'      -- n  :: Int (this cycle's value)
  Signal m <- registerC 8 -< Signal m'      -- m  :: Int
  let n' = n + 1                            -- pure, value-level
      m' = m + 1
  idC -< Signal (n' + m')
```

The plugin collects the value-level bindings into a single pure function,
lifts it to the signal level with `fmap` (using `bundle`/`unbundle` to group
the buses), and ties the feedback knot with a lazy let binding. See
example/ValueCircuits.hs for more examples and the expansion of `counter3`.

Notes:

- Pattern match down to *exactly* the `Signal` layer, no shallower; the
  plugin cannot (yet) know which types contain signals, so the boundary has
  to be explicit. Marking a bus that is not a `Signal` (e.g. a `Vec` of
  signals) is a type error on the offending statement.
- In a `circuitS` block, `let` statements are value-level: they form the body
  of the generated logic function and cannot define new buses or circuits.
- All buses crossing the value boundary must share the same clock domain
  (they are combined with `bundle`).
