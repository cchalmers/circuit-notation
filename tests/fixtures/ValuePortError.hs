{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture with a plugin-level port error in a @circuit@ block: the bus
-- @b@ is bound but never used, so the plugin itself (not GHC's type checker)
-- reports \"Slave port b has no associated master\" -- pointing at the
-- binding.
module ValuePortError where

import           Circuit
import           Clash.Prelude

valuePortError :: Circuit (Signal dom Int) (Signal dom Int)
valuePortError = circuit \(SignalV a) -> do
  b <- idC -< SignalV (a + 1)                         -- value-port-error-marker
  idC -< SignalV (a * 2)
