# Revision history for `circuit-notations`

## Unreleased

* Add value-level circuits via the new `circuitS` keyword. The circuit's
  logic is written over the values sampled each clock cycle (marked with
  `Signal`/`Fwd` patterns and expressions); the plugin lifts it back to the
  signal level with `fmap`/`bundle`/`unbundle` and ties feedback loops with a
  lazy let binding. See the README and example/ValueCircuits.hs.

  A `circuitS` block can span several clock domains: the value-level
  bindings are split into groups connected by shared variables and each
  group is lifted with its own `fmap`/`bundle`/`unbundle`, so only buses
  whose values actually meet must share a domain. Sharing a value across
  domains is rejected by the type checker. Lets that don't touch value land
  stay at the bus level, so let-bound sub-circuits can be used with `-<`.

  The value boundary is generated with the new `SigTag` pattern synonym
  (`Circuit` module), which pins the bus type to a `Signal` so that type
  inference survives nested circuits (the `Fwd` family is not injective) and
  "too shallow" `Signal` markers report a direct `Vec`-vs-`Signal` style
  mismatch. **Breaking**: `ExternalNames` gained a `signalTagName` field, so
  custom plugins (e.g. clash-protocols style) need to supply it.
* Add a per-GHC `checks` output to the flake, so `nix flake check` (or
  `nix build .#checks.<system>.<ghc>`) builds the package and runs all test
  suites against every supported GHC. The CI nix job now uses it. The
  error-location test suite skips itself (with a message) when the ambient
  `ghc` has no circuit-notation package registered — as during a plain nix
  build of the package, where it previously failed.
* Fix the source location of type errors on a bus. Since bus tagging was
  introduced, such errors pointed at the end of the `circuit` block rather than
  at the offending statement. Generated bindings are now located at their
  circuit expression so GHC blames the right line.

## 0.2.0.0 -- 2026-04-23

* Start of the changelog
