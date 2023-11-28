{-# LANGUAGE Arrows #-}

-- This option is a test by itself: if we were to export a plugin with the
-- wrong type or name, GHC would refuse to compile this file.
{-# OPTIONS -fplugin=CircuitNotation #-}

module Main where

import           Circuit
import           Clash.Prelude

main :: IO ()
main = pure ()

testIdCircuit :: Circuit (Signal dom Bool) (Signal dom Bool)
testIdCircuit = circuit $ \x -> x

-- test that signals can be duplicated
testDupCircuit :: Circuit (Signal dom Bool) (Signal dom Bool, Signal dom Bool)
testDupCircuit = circuit $ \x -> (x, x)

testDup2Circuit :: Circuit (Signal dom Bool) (Signal dom Bool, Signal dom Bool, Signal dom Bool)
testDup2Circuit = circuit $ \x -> do
    y <- idC -< x
    idC -< (y, y, x)
