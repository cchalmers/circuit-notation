{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture where a value-level @let@ in a @circuit@ block is never used as
-- an output: @bad = not a@ where @a@ is an 'Int' sampled off the input bus.
-- Such a value group has no outputs, so its logic used to be dropped entirely
-- and the broken @let@ was silently accepted. Its logic is now still bound (to
-- a wildcard) so the group is typechecked; with nothing downstream to pin @a@,
-- the @Int@-vs-@Bool@ mismatch surfaces where the input value enters the
-- circuit (the @SignalV a@ marker), rather than being accepted.
module DeadLetError where

import           Circuit
import           Clash.Prelude
import qualified Prelude       as P

deadLetError :: Circuit (Signal dom Int) (Signal dom Bool)
deadLetError = circuit \(SignalV a) -> do  -- dead-let-error-marker
  let bad = P.not a
  idC -< SignalV True
