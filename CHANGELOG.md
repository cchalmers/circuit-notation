# Revision history for `circuit-notations`

## 0.3.0.0 -- Unreleased

* Add value-level ports via the new `SignalV` and `FwdV` markers in
  `circuit` blocks. The circuit's logic is written over the values sampled
  each clock cycle; the plugin lifts it back to the signal level with
  `fmap`/`bundle`/`unbundle` and ties feedback loops with a lazy let
  binding. The bus-level markers still bind the raw forward channel and mix
  freely with value markers in one block; `Fwd` works on any bus, while the
  bus-level `Signal` (and new `DSignal`) markers now additionally enforce
  the bus type, which also drives type inference. See the README and
  example/ValueCircuits.hs.

  **Breaking**: `ExternalNames` gained `signalTagName`, `fwdTagName` and
  `dSignalTagName` fields, so custom plugins (e.g. clash-protocols style)
  need to supply them — `defExternalNames` is now exported so they can be
  record updates of the defaults.
* Add a per-GHC `checks` output to the flake, so `nix flake check` (or
  `nix build .#checks.<system>.<ghc>`) builds the package and runs all test
  suites against every supported GHC. The CI nix job now uses it. The
  error-location test suite skips itself (with a message) when the ambient
  `ghc` has no circuit-notation package registered — as during a plain nix
  build of the package, where it previously failed.
* Fix the source location of type errors on a bus. Since bus tagging was
  introduced, such errors pointed at the end of the `circuit` block rather than
  at the offending statement. Generated bindings are now located at their
  circuit expression so GHC blames the right line. Generated bundle patterns
  and expressions also take the span of the ports they bundle, so
  whole-bundle errors (e.g. sharing a value-level variable across clock
  domains) are blamed on the ports rather than on the head of the circuit.

## 0.2.0.0 -- 2026-04-23

* Start of the changelog
