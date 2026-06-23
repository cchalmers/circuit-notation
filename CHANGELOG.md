# Revision history for `circuit-notations`

## Unreleased

* Fix the source location of type errors on a bus. Since bus tagging was
  introduced, such errors pointed at the end of the `circuit` block rather than
  at the offending statement. Generated bindings are now located at their
  circuit expression so GHC blames the right line.

## 0.2.0.0 -- 2026-04-23

* Start of the changelog
