{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture mixing plain (@SignalV@) and delayed (@DSignalV@) value
-- markers in one logic group: neither the plain nor the delayed bundle
-- accepts both bus kinds, so the plugin itself reports the conflict --
-- pointing at the offending @DSignalV@ marker.
module MixedMarkerError where

import           Circuit
import           Clash.Prelude

mixedMarkerError :: Circuit (Signal dom Int, DSignal dom 0 Int) (Signal dom Int)
mixedMarkerError = circuit
  \( SignalV a
   , DSignalV b                                      -- mixed-marker-error-marker
   ) -> do
    idC -< SignalV (a + b)
