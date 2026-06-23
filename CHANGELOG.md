# Revision history for `circuit-notations`

## Unreleased

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
