{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture marking a non-signal bus with @Signal@ in a @circuitV@ block:
-- @vecC@ produces a @Vec@ of signals, so the @Signal v@ pattern is \"too
-- shallow\" (the value boundary must sit exactly at a 'Signal'). The
-- generated @SigTag@ pins the bus type to a signal, so GHC reports a clear
-- @Vec ... /~ Signal ...@ mismatch; this asserts it points at the offending
-- statement.
module ValueShapeError where

import           Circuit
import           Clash.Prelude

vecC :: Circuit (Signal dom Int) (Vec 2 (Signal dom Int))
vecC = Circuit $ \(s :-> _) -> (() :-> (s :> s :> Nil))

valueShapeError :: Circuit (Signal dom Int) (Signal dom Int)
valueShapeError = circuitV \(Signal a) -> do
  Signal v <- vecC -< Signal (a + 1)                 -- value-shape-error-marker
  idC -< Signal (a + 1)
