-- This option is a test by itself: if we were to export a plugin with the
-- wrong type or name, GHC would refuse to compile this file.
{-# OPTIONS -fplugin=CircuitNotation #-}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import           Control.Monad   (unless)
import           System.Exit     (exitFailure)

import           Clash.Prelude   (System, fromList, sampleN)

import           Circuit
import           Example         ()
import           ValueCircuits

main :: IO ()
main = do
  results <- mapM check
    [ ("plusOne",          sim plusOne          (fromList [0..]), [1, 2, 3, 4, 5])
    , ("counter",          sampleN 5 (simulateUnitCircuit @System counter), [0, 1, 2, 3, 4])
    , ("accum",            sim accum            (fromList [1..]), [1, 3, 6, 10, 15])
    , ("counter3",         sim counter3         (pure False),     [10, 12, 14, 16, 18])
    , ("counter3Expanded", sim counter3Expanded (pure False),     [10, 12, 14, 16, 18])
    ]
  unless (and results) exitFailure
 where
  sim c = sampleN 5 . simulateSigCircuit @System c

  check :: (String, [Int], [Int]) -> IO Bool
  check (name, actual, expected)
    | actual == expected = pure True
    | otherwise = do
        putStrLn $ name <> ": expected " <> show expected <> " but got " <> show actual
        pure False
