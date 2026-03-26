#!/usr/bin/env runhaskell

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}

import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util
import Data.Tuple (swap)
import Data.List (isSuffixOf, isInfixOf, isPrefixOf, stripPrefix, unsnoc, find, intercalate)
import Data.Bifunctor (bimap)
import Data.Char (isDigit)
import Data.Maybe (isJust, fromMaybe)
import Control.Monad (forM, forM_, guard, join)
import System.Directory qualified as SD
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Text.Printf (printf)
import System.Exit(ExitCode(..))
import Data.Function ((&))
import Debug.Trace

vera :: FilePath
vera = "_build/install/default/bin/vera"

-- | Timeout for vera runs (in seconds)
veraTimeout :: Double
veraTimeout = 5

-- | Value of --solver= flag for vera
veraSolver :: String
veraSolver = "bitwuzla"

-- | Standard power-of-two sizes, plus some weird ones for variety
runSizes :: [Int]
-- runSizes = [4,5,8,12,16,32,43,64,128]
runSizes = [4,8]

main :: IO ()
main = shakeArgs shakeOptions {shakeThreads=0} $ do
  phony "clean" $ do
    need ["clean-synth", "clean-gen", "clean-run"]
    removeFilesAfterVerbose "" ["examples/summary.csv"]

  phony "synth" $ do
    sources <- filter (not . (".synth.sv" `isSuffixOf`))
      <$> getDirectoryFiles "." ["examples//*.sv"]
    let targets = map (-<.> "synth.sv") sources
    need targets

  phony "clean-synth" $ do
    removeFilesAfterVerbose "examples" ["//*.synth.sv", "//*.synth.log"]

  -- Run yosys synthesis. Needs to take priority over the gen_ rule
  -- below, since they both match gen_*/*.synth.sv
  priority 2 $ "examples//*.synth.sv" %> \out -> do
    let src = dropExtensions out <> ".sv"
    let log = dropExtensions out <> ".synth.log"
    need ["examples/synth.tcl", src]
    cmd_
      (Traced "yosys")
      (AddEnv "SV_INPUT" src)
      (AddEnv "SV_OUTPUT" out)
      (FileStdout log)
      (FileStderr log)
      "yosys" "-c" "examples/synth.tcl"

  -- gen_<category>_<N>/<module>.sv -> templates/<category>/<module>.sv.j2
  "examples/gen_*/*.sv" %> \out -> do
    let Just (template, size) = templateForInstantiation out
        log = out -<.> "gen.log"
    need [template]
    cmd_
      (Traced "jinja")
      (FileStdout out)
      (FileStderr log)
      "jinja2" "-D" ("N=" <> show size) template

  -- examples/gen_*/all
  phonys $ \out -> case splitDirectories out of
    ["examples", genDir, "all"] -> do
      (templateName, size) <- parseTemplateDir genDir
      Just $ do
        templates <- getDirectoryFiles ("examples" </> "templates" </> templateName) ["*.sv.j2"]
        need [ "examples" </> genDir </> dropExtension template | template <- templates ]
    _ -> Nothing

  phony "clean-gen" $ do
    genDirs <- filter ("gen_" `isPrefixOf`) <$> getDirectoryDirs "examples"
    forM_ genDirs $ \dir -> do
      putInfo $ "Removing " <> ("examples" </> dir) <> "/"
      runAfter $ SD.removeDirectoryRecursive ("examples" </> dir)

  -- Running vera
  "//*.vera.time" %> \out -> need [ out -<.> "log" ]
  "//*.vera.smt2" %> \out -> need [ out -<.> "log" ]
  "//*_vs_*.vera.log" %> \out -> do
    let Just [dir, mod1, mod2] = filePattern "//*_vs_*.vera.log" out
        smtFile = out -<.> "smt2"
        timeFile = out -<.> "time"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    need [vera, left, right]
    begin <- liftIO getCurrentTime
    (Exit exitCode) <- cmd
      (Traced "vera")
      (Timeout veraTimeout)
      (FileStdout out)
      (FileStderr out)
      (AddEnv "OCAMLRUNPARAM" "b")
      "time" vera "compare" ("--solver=" ++ veraSolver) ("--dump-query=" ++ smtFile) left right
    case exitCode of
      ExitFailure 130 -> liftIO $ appendFile out "Timed out"
      _ -> pure ()
    end <- liftIO getCurrentTime
    writeFile' timeFile (show (diffUTCTime end begin))

  phony "vera" $ need [vera]
  vera %> \out -> do
    need =<< getDirectoryFiles "" ["*.v", "*.ml"]
    cmd_ "dune" "build"

  phony "clean-run" $ do
    removeFilesAfterVerbose "examples"
      ["//*.vera.log", "//*.vera.time", "//*.vera.smt2"]

  "examples/summary.csv" %> \out -> do
    concreteExampleDirs :: [String] <-
      filter (\dir -> dir `notElem` ["templates"] && not ("gen_" `isPrefixOf` dir))
        <$> getDirectoryDirs "examples"
    concreteExamples <- fmap join <$> forM concreteExampleDirs $ \exampleDir -> do
      baseModuleFiles <- getDirectoryFiles ("examples" </> exampleDir) ["*.sv"]
      let moduleNames =
            baseModuleFiles
            & filter (not . (".synth.sv" `isSuffixOf`))
            & map dropExtensions
            & map (\m -> [m, m <.> "synth"])
            & join
      return
        [ (exampleDir, left, right)
        | (left, right) <- allPairs moduleNames
        ]
    templateExampleDirs <- getDirectoryDirs ("examples" </> "templates")
    templateExamples <- fmap join <$> forM templateExampleDirs $ \exampleTemplateDir -> do
      moduleTemplates <- getDirectoryFiles ("examples" </> "templates" </> exampleTemplateDir) ["*.sv.j2"]
      let moduleNames =
            moduleTemplates
            & map dropExtensions
            & map (\m -> [m, m <.> "synth"])
            & join
      let exampleDir size = "gen_" <> exampleTemplateDir <> "_" <> show size
      return
        [ (exampleDir size, left, right)
        | (left, right) <- allPairs moduleNames
        , size <- runSizes
        ]
    let examples = concreteExamples ++ templateExamples
    let logFiles =
          [ "examples" </> dir </> (left ++ "_vs_" ++ right ++ ".vera.log")
            | (dir, left, right) <- examples
          ]
    let timeFiles = map (-<.> "time") logFiles
    logs <- forP logFiles readFileLines
    let results =
          [ if
              | "Equivalent (UNSAT)" `elem` logLines -> "Equivalent"
              | "Non-equivalent (SAT)" `elem` logLines -> "Non-equivalent"
              | "Timed out" `elem` logLines -> "Timed out"
              | Just errorLine <- find ("Error" `isPrefixOf`) logLines -> errorLine
              | ("Stack overflow" `isInfixOf`) `any` logLines -> "Stack overflow"
              | otherwise -> "??"
            | logLines <- logs
          ]
    times <- forP timeFiles readFile'
    writeFileLines out
      [ intercalate "," [dir, left, right, result, time]
      | ((dir, left, right), result, time) <- zip3 examples results times
      ]


-- Helpers

-- Split the list on the first instance of the separator
splitOn :: Eq a => a -> [a] -> ([a], [a])
splitOn p lst =
  ( takeWhile (/= p) $ lst
  , tailSafe . dropWhile (/= p) $ lst
  )
  where tailSafe [] = []
        tailSafe (x:xs) = xs

-- Split the list on the last instance of the separator
splitOnLast :: Eq a => a -> [a] -> ([a], [a])
splitOnLast p = swap . bimap reverse reverse . splitOn p . reverse

-- | gen_<category>_<N> -> Just (<category>, <N>)
parseTemplateDir :: String -> Maybe (String, Int)
parseTemplateDir name = do
  withoutGen <- stripPrefix "gen_" name
  let (category, widthPart) = splitOn '_' withoutGen
  if not (null widthPart) && all isDigit widthPart && not (null category)
    then Just (category, read widthPart)
    else Nothing

-- .../gen_<category>_<N>/<module>.sv -> Just (.../templates/<category>/<module>.sv.j2, N)
templateForInstantiation :: FilePath -> Maybe (FilePath, Int)
templateForInstantiation (splitDirectories -> Snoc (Snoc rest dir) file) = do
  (category, size) <- parseTemplateDir dir
  Just (joinPath rest </> "templates" </> category </> file <> ".j2", size)
templateForInstantiation _ = Nothing

isTemplateInstantiation :: FilePath -> Bool
isTemplateInstantiation = isJust . templateForInstantiation

removeFilesAfterVerbose :: FilePath -> [FilePattern] -> Action ()
removeFilesAfterVerbose dir pat = do
  synthFiles <- getDirectoryFiles dir pat
  mapM_ (\f -> putInfo $ "Removing " <> f) synthFiles
  removeFilesAfter dir pat

pattern Snoc :: [a] -> a -> [a]
pattern Snoc xs x <- (unsnoc -> Just (xs, x))

allPairs :: [a] -> [(a, a)]
allPairs [] = []
allPairs (x:xs) = map (x,) xs ++ allPairs xs
