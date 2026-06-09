# Revision history for `circuit-notations`

## Unreleased

* Add value-level circuits via the new `circuitS` keyword. The circuit's
  logic is written over the values sampled each clock cycle (marked with
  `Signal`/`Fwd` patterns and expressions); the plugin lifts it back to the
  signal level with `fmap`/`bundle`/`unbundle` and ties feedback loops with a
  lazy let binding. See the README and example/ValueCircuits.hs.
* Fix the source location of type errors on a bus. Since bus tagging was
  introduced, such errors pointed at the end of the `circuit` block rather than
  at the offending statement. Generated bindings are now located at their
  circuit expression so GHC blames the right line.

## 0.2.0.0 -- 2026-04-23

* Start of the changelog
