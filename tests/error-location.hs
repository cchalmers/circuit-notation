-- | Regression tests for the source locations of error messages.
--
-- When bus tagging (the @BusTag@ wrapping) was introduced, type errors on a
-- bus stopped pointing at the offending statement and instead pointed at the
-- end of the @circuit@ block, which made them very hard to act on. The same
-- concern applies to @circuitS@ blocks, where the value-level expressions and
-- lets are moved into a generated @circuitLogic@ function.
--
-- Each fixture in 'fixtures' deliberately fails to compile, with the
-- offending statement tagged by a marker comment that appears on exactly one
-- line. The fixture is compiled with the plugin enabled and we assert that an
-- error is reported /on that line/ (and, optionally, that the output contains
-- an expected message). It uses the same plain @ghc@ +
-- package-environment-file mechanism that CI already uses to compile the
-- @Example@ module.
module Main (main) where

import           Control.Monad      (forM, unless, when)
import           Data.List          (isInfixOf, isPrefixOf, nub, sort)
import           Data.Maybe         (mapMaybe)
import           System.Directory   (getTemporaryDirectory)
import           System.Environment (lookupEnv)
import           System.Exit        (exitFailure)
import           System.FilePath    ((</>))
import           System.Process     (readProcessWithExitCode)
import           Text.Read          (readMaybe)

data Fixture = Fixture
  { fixturePath   :: FilePath
  -- ^ the file to compile, which must fail to compile
  , fixtureMarker :: String
  -- ^ marker comment on the line the error should be reported on; it must
  -- appear on exactly one line of the fixture
  , fixtureNeedle :: Maybe String
  -- ^ optionally, a string the compiler output must contain
  }

fixtures :: [Fixture]
fixtures =
  [ -- type error on a bus in an ordinary circuit
    Fixture ("tests" </> "fixtures" </> "BusError.hs") "bus-error-marker" Nothing
    -- type error on a value-level expression in a circuitS
  , Fixture ("tests" </> "fixtures" </> "ValueExprError.hs") "value-expr-error-marker" Nothing
    -- type error inside a value-level let in a circuitS
  , Fixture ("tests" </> "fixtures" </> "ValueLetError.hs") "value-let-error-marker" Nothing
    -- port error reported by the plugin itself in a circuitS
  , Fixture ("tests" </> "fixtures" </> "ValuePortError.hs") "value-port-error-marker"
      (Just "has no associated master")
    -- a Signal marker on a bus that is not a signal (the marker is "too
    -- shallow"); the SigTag the plugin generates should turn this into a
    -- direct Vec-vs-Signal mismatch on the offending pattern
  , Fixture ("tests" </> "fixtures" </> "ValueShapeError.hs") "value-shape-error-marker" Nothing
    -- sharing a value-level variable across two clock domains; the merged
    -- group's bundle demands one domain, so this must be a domain-mismatch
    -- type error
  , Fixture ("tests" </> "fixtures" </> "CrossDomainError.hs") "cross-domain-error-marker"
      (Just "Couldn't match type")
  ]

main :: IO ()
main = do
  ghc <- maybe "ghc" id <$> lookupEnv "GHC"
  results <- forM fixtures (checkFixture ghc)
  unless (and results) exitFailure

checkFixture :: String -> Fixture -> IO Bool
checkFixture ghc (Fixture fixture marker needle) = do
  src <- readFile fixture

  -- Work out which line the deliberate error is on by finding the marker.
  let markedLines =
        [ n | (n, l) <- zip [1 :: Int ..] (lines src), marker `isInfixOf` l ]
  expectedLine <- case markedLines of
    [n] -> pure n
    _   -> die $ "expected exactly one line containing " <> show marker
                   <> " in " <> fixture <> ", found lines " <> show markedLines

  -- Compile the fixture and collect the reported error lines.
  tmp <- getTemporaryDirectory
  let args =
        [ "-outputdir", tmp </> "circuit-notation-error-test"
        , "-itests/fixtures"
        , fixture
        ]
  (_code, out, err) <- readProcessWithExitCode ghc args ""
  let output    = out <> err
      errLines  = sort . nub $ errorLineNumbers fixture output

  putStrLn $ fixture <> ":"
  putStrLn $ "  ghc reported errors on lines: " <> show errLines
  putStrLn $ "  expected an error on line:    " <> show expectedLine

  when (null errLines) $
    die $ "expected the fixture to fail to compile, but ghc reported no\n\
          \error locations. Full output:\n" <> output

  unless (expectedLine `elem` errLines) $
    die $ "the error was not reported on the offending line ("
            <> show expectedLine <> ").\n"
            <> "Instead it was reported on lines " <> show errLines
            <> " -- this is the regression where errors point at\n"
            <> "the end of the circuit rather than the actual mistake.\n\n"
            <> "Full ghc output:\n" <> output

  case needle of
    Just msg | not (msg `isInfixOf` output) ->
      die $ "expected the compiler output to mention " <> show msg
              <> ".\n\nFull ghc output:\n" <> output
    _ -> pure ()

  putStrLn "  OK: error points at the offending statement."
  pure True

-- | Extract the line numbers from GHC error messages that refer to the fixture,
-- e.g. a line @tests/fixtures/BusError.hs:30:8: error: ...@ yields @30@.
errorLineNumbers :: FilePath -> String -> [Int]
errorLineNumbers fixture = mapMaybe parseLine . lines
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
