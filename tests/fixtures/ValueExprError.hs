{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture with a deliberate type error on a /value-level/ expression in a
-- @circuit@ block: @a@ is an 'Int' (sampled off the input bus) but is used
-- with @(&&)@. The erroring statement is not the last statement of the
-- circuit; the error-location test asserts GHC points at the tagged line and
-- not at the end of the block (where the generated @circuitLogic@ and
-- knot-tying bindings live).
module ValueExprError where

import           Circuit
import           Clash.Prelude
import           Clash.Signal.Internal (Signal ((:-)))

registerC :: a -> Circuit (Signal dom a) (Signal dom a)
registerC a = Circuit $ \(s :-> ()) -> (() :-> (a :- s))

valueExprError :: Circuit (Signal dom Int) (Signal dom Int)
valueExprError = circuit \(SignalV a) -> do
  SignalV b <- registerC 0 -< SignalV (a && True)      -- value-expr-error-marker
  idC -< SignalV (b + a)
