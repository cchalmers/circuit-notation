{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture sharing a value-level variable between two 'DSignal' buses at
-- /different/ pipeline depths: @a + b@ mixes a delay-0 and a delay-1 value.
-- The shared variables put both buses in the same logic group, whose
-- delayed bundle demands a single delay index, so GHC reports a
-- @0@-vs-@1@ mismatch. Like the cross-domain case, the blame lands on the
-- head of the circuit.
module CrossDelayError where

import           Circuit
import           Clash.Prelude

crossDelayError :: Circuit (DSignal dom 0 Int, DSignal dom 1 Int) (DSignal dom 0 Int)
crossDelayError = circuit \(DSignalV a, DSignalV b) -> do  -- cross-delay-error-marker
  idC -< DSignalV (a + b)
