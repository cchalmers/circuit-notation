# Revision history for `circuit-notations`

## Unreleased

* Add value-level circuits via the new `circuitS` keyword. The circuit's
  logic is written over the values sampled each clock cycle (marked with
  `Signal`/`Fwd` patterns and expressions); the plugin lifts it back to the
  signal level with `fmap`/`bundle`/`unbundle` and ties feedback loops with a
  lazy let binding. See the README and example/ValueCircuits.hs.

  The value boundary is generated with the new `SigTag` pattern synonym
  (`Circuit` module), which pins the bus type to a `Signal` so that type
  inference survives nested circuits (the `Fwd` family is not injective) and
  "too shallow" `Signal` markers report a direct `Vec`-vs-`Signal` style
  mismatch. **Breaking**: `ExternalNames` gained a `signalTagName` field, so
  custom plugins (e.g. clash-protocols style) need to supply it.
* Fix the source location of type errors on a bus. Since bus tagging was
  introduced, such errors pointed at the end of the `circuit` block rather than
  at the offending statement. Generated bindings are now located at their
  circuit expression so GHC blames the right line.

## 0.2.0.0 -- 2026-04-23

* Start of the changelog
