{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture sharing a value-level variable across two clock domains in a
-- @circuitV@ block: @acc + a + b@ mixes values sampled from a @domA@ bus and
-- a @domB@ bus, which is an (unsynchronized) clock domain crossing. The
-- shared variables put both buses in the same logic group, whose @bundle@
-- demands a single domain, so GHC reports @Couldn't match type domA with
-- domB@. The blame lands on the head of the circuit (the constraint solver
-- unifies the domains via the generated bundle before it checks the slave
-- pattern), so the marker sits on the @circuitV@ line.
module CrossDomainError where

import           Circuit
import           Clash.Prelude
import           Clash.Signal.Internal (Signal ((:-)))

registerC :: a -> Circuit (Signal dom a) (Signal dom a)
registerC a = Circuit $ \(s :-> ()) -> (() :-> (a :- s))

crossDomainError :: Circuit (Signal domA Int, Signal domB Int) (Signal domA Int)
crossDomainError = circuitV \(Signal a, Signal b) -> do  -- cross-domain-error-marker
  Signal acc <- registerC 0 -< Signal (acc + a + b)
  idC -< Signal acc
