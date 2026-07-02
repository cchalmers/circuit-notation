{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture with a deliberate type error inside a /value-level let/ of a
-- @circuit@ block: @a@ is an 'Int' (sampled off the input bus) but is
-- passed to 'not'. The let bindings move into the generated @circuitLogic@
-- function; this asserts they keep their source locations when they do.
module ValueLetError where

import           Circuit
import           Clash.Prelude

valueLetError :: Circuit (Signal dom Int) (Signal dom Int)
valueLetError = circuit \(SignalV a) -> do
  let b = not a                                      -- value-let-error-marker
  idC -< SignalV (a + (if b then 1 else 0))
