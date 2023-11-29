-- This option is a test by itself: if we were to export a plugin with the
-- wrong type or name, GHC would refuse to compile this file.
{-# OPTIONS -fplugin=CircuitNotation #-}

module Main where

import           Circuit

main :: IO ()
main = pure ()
