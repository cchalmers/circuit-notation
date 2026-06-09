-- This option is a test by itself: if we were to export a plugin with the
-- wrong type or name, GHC would refuse to compile this file.
{-# OPTIONS -fplugin=CircuitNotation #-}

{-# LANGUAGE DataKinds #-}

module Main where

import           Control.Monad (unless)
import           System.Exit   (exitFailure)

import           Clash.Prelude (NFDataX, Signal, System, Vec ((:>), Nil),
                                fromList, sampleN)

import           Example       ()
import           ValueCircuits

sample5 :: NFDataX a => Signal System a -> [a]
sample5 = sampleN 5

check :: (Eq a, Show a) => String -> a -> a -> IO Bool
check name actual expected
  | actual == expected = pure True
  | otherwise = do
      putStrLn $ name <> ": expected " <> show expected <> " but got " <> show actual
      pure False

main :: IO ()
main = do
  let (fanA, fanB)     = simulateC fanOutC (fromList [0 ..])
      (splitA, splitB) = simulateC splitC (fromList [(i, even i) | i <- [0 ..]])
      (mixA, mixB)     = simulateC mixedC (fromList [0 ..], fromList [5 ..])
      (mcA, mcB)       = simulateC multicastC (fromList [0 ..])

  results <- sequence
    -- basic shapes
    [ check "plusOne"    (sample5 (simulateC plusOne (fromList [0 ..])))    [1, 2, 3, 4, 5]
    , check "plusOneFwd" (sample5 (simulateC plusOneFwd (fromList [0 ..]))) [1, 2, 3, 4, 5]
    , check "alwaysFive" (sample5 (simulateC alwaysFive ()))                [5, 5, 5, 5, 5]
    , check "addC"       (sample5 (simulateC addC (fromList [1 ..], fromList [10, 20 ..])))
                         [11, 22, 33, 44, 55]
    , check "fanOutC"    (sample5 fanA, sample5 fanB)
                         ([1, 2, 3, 4, 5], [0, 2, 4, 6, 8])
    , check "splitC"     (sample5 splitA, sample5 splitB)
                         ([0, 1, 2, 3, 4], [True, False, True, False, True])
    , check "joinC"      (sample5 (simulateC joinC (fromList [1 ..], fromList [even i | i <- [0 :: Int ..]])))
                         [(1, True), (2, False), (3, True), (4, False), (5, True)]
    , check "nestedTupleC"
        (sample5 (simulateC nestedTupleC ((fromList [1 ..], fromList [10, 20 ..]), pure 2)))
        [21, 42, 63, 84, 105]
    , check "vecInC"     (sample5 (simulateC vecInC (fromList [10, 20 ..] :> fromList [1 ..] :> Nil)))
                         [9, 18, 27, 36, 45]
    , check "vecOutC"    (fmap sample5 (simulateC vecOutC (fromList [0 ..])))
                         ([1, 2, 3, 4, 5] :> [-1, 0, 1, 2, 3] :> Nil)
    , check "annotatedC" (sample5 (simulateC annotatedC (fromList [0 ..]))) [1, 2, 3, 4, 5]

    -- feedback
    , check "counter"          (sample5 (simulateC counter ()))                 [0, 1, 2, 3, 4]
    , check "accum"            (sample5 (simulateC accum (fromList [1 ..])))    [1, 3, 6, 10, 15]
    , check "counter3"         (sample5 (simulateC counter3 (pure False)))      [10, 12, 14, 16, 18]
    , check "counter3Expanded" (sample5 (simulateC counter3Expanded (pure False))) [10, 12, 14, 16, 18]
    , check "fibC"             (sample5 (simulateC fibC ()))                    [0, 1, 1, 2, 3]
    , check "shift3"           (sample5 (simulateC shift3 (fromList [1 ..])))   [0, 0, 0, 1, 2]
    , check "rotate3"          (sample5 (simulateC rotate3 (pure 1)))           [6, 7, 8, 9, 10]

    -- mixing value land and bus land
    , check "mixedC"      (sample5 mixA, sample5 mixB) ([1, 2, 3, 4, 5], [5, 6, 7, 8, 9])
    , check "multicastC"  (sample5 mcA, sample5 mcB)   ([1, 2, 3, 4, 5], [1, 2, 3, 4, 5])
    , check "passthrough" (sample5 (simulateC passthrough (fromList [3 ..]))) [3, 4, 5, 6, 7]

    -- nesting
    , check "nestedSInCircuit" (sample5 (simulateC nestedSInCircuit (fromList [0 ..]))) [0, 2, 4, 6, 8]
    , check "nestedCircuitInS" (sample5 (simulateC nestedCircuitInS (fromList [0 ..]))) [3, 6, 9, 12, 15]
    , check "nestedSInS"       (sample5 (simulateC nestedSInS (fromList [0 ..])))       [2, 4, 6, 8, 10]
    ]

  putStrLn $ "passed " <> show (length (filter id results)) <> "/" <> show (length results)
  unless (and results) exitFailure
