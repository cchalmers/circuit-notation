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

  A block can span several clock domains: the value-level bindings are
  split into groups connected by shared variables and each group is lifted
  with its own `fmap`/`bundle`/`unbundle`, so only buses whose values
  actually meet must share a domain. Sharing a value across domains is
  rejected by the type checker. Lets that don't touch value land stay at
  the bus level, so let-bound sub-circuits can be used with `-<`.

  The value markers have distinct semantics: `SignalV x` asserts the
  bus is a `Signal` (best inference — it works against fully generic
  sub-circuits); `FwdV x` samples/drives the forward channel of any
  signal-like bus via the new `SignalBus` class (`Signal`s, `Vec`s and
  tuples of them, custom buses) but needs the bus type determined by
  context; and `DSignalV x` is `SignalV` for delayed signals — the delay
  index is part of the bus type, so a logic group's values must all sit at
  the same pipeline depth, and its outputs are produced at that depth.
  Mixing plain and delayed markers in one group is reported by the plugin.

  The value boundary is generated with the new `SigTag`, `FwdTag` and
  `DSigTag` pattern synonyms (`Circuit` module); `SigTag`/`DSigTag` pin the
  bus type so that type inference survives nested circuits (the `Fwd`
  family is not injective) and "too shallow" `SignalV` markers report a
  direct `Vec`-vs-`Signal` style mismatch. **Breaking**: `ExternalNames`
  gained `signalTagName`, `fwdTagName` and `dSignalTagName` fields, so
  custom plugins (e.g. clash-protocols style) need to supply them —
  `defExternalNames` is now exported so they can be record updates of the
  defaults.
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
