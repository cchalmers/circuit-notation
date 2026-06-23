-- | Regression test for the source locations of type errors on buses.
--
-- When bus tagging (the @BusTag@ wrapping) was introduced, type errors on a
-- bus stopped pointing at the offending statement and instead pointed at the
-- end of the @circuit@ block, which made them very hard to act on.
--
-- This test compiles 'tests/fixtures/BusError.hs' (which has a deliberate type
-- error on a bus, on the line marked @ERROR HERE@) with plugin enabled and
-- asserts that GHC reports an error /on that line/. It uses the same plain
-- @ghc@ + package-environment-file mechanism that CI already uses to compile
-- the @Example@ module.
module Main (main) where

import           Control.Monad      (unless, when)
import           Data.List          (isInfixOf, isPrefixOf, nub, sort)
import           Data.Maybe         (mapMaybe)
import           System.Directory   (getTemporaryDirectory)
import           System.Environment (lookupEnv)
import           System.Exit        (exitFailure)
import           System.FilePath    ((</>))
import           System.Process     (readProcessWithExitCode)
import           Text.Read          (readMaybe)

fixture :: FilePath
fixture = "tests" </> "fixtures" </> "BusError.hs"

-- | The marker placed on the erroring statement inside the fixture. It is
-- chosen so that it appears on exactly one line of the fixture.
marker :: String
marker = "bus-error-marker"

main :: IO ()
main = do
  src <- readFile fixture

  -- Work out which line the deliberate error is on by finding the marker.
  let markedLines =
        [ n | (n, l) <- zip [1 :: Int ..] (lines src), marker `isInfixOf` l ]
  expectedLine <- case markedLines of
    [n] -> pure n
    _   -> die $ "expected exactly one line containing " <> show marker
                   <> " in " <> fixture <> ", found lines " <> show markedLines

  -- Compile the fixture and collect the reported error lines.
  ghc <- maybe "ghc" id <$> lookupEnv "GHC"
  tmp <- getTemporaryDirectory
  let args =
        [ "-outputdir", tmp </> "circuit-notation-error-test"
        , "-itests/fixtures"
        , fixture
        ]
  (_code, out, err) <- readProcessWithExitCode ghc args ""
  let output    = out <> err
      errLines  = sort . nub $ errorLineNumbers output

  putStrLn $ "ghc reported errors on lines: " <> show errLines
  putStrLn $ "expected an error on line:    " <> show expectedLine

  when (null errLines) $
    die $ "expected the fixture to fail to compile, but ghc reported no\n\
          \error locations. Full output:\n" <> output

  unless (expectedLine `elem` errLines) $
    die $ "type error on the bus was not reported on the offending line ("
            <> show expectedLine <> ").\n"
            <> "Instead it was reported on lines " <> show errLines
            <> " -- this is the bus-tagging regression where errors point at\n"
            <> "the end of the circuit rather than the actual mistake.\n\n"
            <> "Full ghc output:\n" <> output

  putStrLn "OK: bus type error points at the offending statement."

-- | Extract the line numbers from GHC error messages that refer to the fixture,
-- e.g. a line @tests/fixtures/BusError.hs:30:8: error: ...@ yields @30@.
errorLineNumbers :: String -> [Int]
errorLineNumbers = mapMaybe parseLine . lines
  where
    parseLine l = do
      let l' = dropWhile (== ' ') l
      rest <- stripFixturePrefix l'
      let lineStr = takeWhile (/= ':') rest
      readMaybe lineStr

    stripFixturePrefix l
      | (fixture <> ":") `isPrefixOf` l = Just (drop (length fixture + 1) l)
      | otherwise                       = Nothing

die :: String -> IO a
die msg = do
  putStrLn ("error-location test failed: " <> msg)
  exitFailure
