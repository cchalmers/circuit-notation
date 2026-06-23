{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS -fplugin=CircuitNotation #-}

-- | A fixture that deliberately contains a type error on a bus, used by the
-- error-location test. The error is on the statement tagged with the marker
-- comment below: @boolC@ forces its input to be a
-- @Signal dom Bool@, but the bus @b@ carries a @Signal dom Int@.
--
-- Crucially the erroring statement is /not/ the last statement of the circuit.
-- Before bus tagging gained source locations, GHC blamed the final statement
-- of the circuit (the @idC -< e@ line) instead of the actual mismatch, which
-- made the error very hard to track down. The test asserts that GHC points at
-- the tagged line.
module BusError where

import           Circuit
import           Clash.Prelude

boolC :: Circuit (Signal dom Bool) (Signal dom Bool)
boolC = idC

busError :: Circuit (Signal dom Int) (Signal dom Int)
busError = circuit $ \a -> do
  b <- idC -< a
  c <- boolC -< b      -- bus-error-marker
  d <- idC -< c
  e <- idC -< d
  idC -< e
