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
import Control.Monad (forM, forM_, guard, join, when)
import System.Directory qualified as SD
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Text.Printf (printf)
import System.Exit(ExitCode(..))
import Data.Function ((&))
import Debug.Trace

vera :: FilePath
vera = "_build/install/default/bin/vera"

-- | Timeout for vera/eqy runs (in seconds)
timeout :: Double
timeout = 600

-- | Timeout for yosys synthesis (NOT symbiyosys/eqy equivalence checking)
yosysTimeout :: Double
yosysTimeout = 600

-- | Value of --solver= flag for vera
veraSolver :: String
-- veraSolver = "bitwuzla" -- Broken with symbiyosys
veraSolver = "cvc5"

-- | Sizes which templated examples will be evaluated at
runSizes :: [Int]
runSizes = [4..64]

main :: IO ()
main = shakeArgs shakeOptions {shakeThreads=0} $ do
  phony "clean" $ do
    need ["clean-synth", "clean-run"]
    removeFilesAfter "" ["examples/summary.csv"]
    removeFilesAfter "examples/out" ["//"]

  phony "synth" $ do
    sources <- filter (not . (".synth.sv" `isSuffixOf`))
      <$> getDirectoryFiles "." ["examples//*.sv"]
    let targets = map (-<.> "synth.sv") sources
    need targets

  phony "clean-synth" $ do
    removeFilesAfter "examples" ["//*.synth.sv", "//*.synth.log"]

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
      (Timeout yosysTimeout)
      (FileStdout log)
      (FileStderr log)
      "yosys" "-c" "examples/synth.tcl"

  -- gen_<category>_<N>/<module>.sv -> templates/<category>/<module>.sv.j2
  "examples/out/gen_*/*.sv" %> \out -> do
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
    ["examples", "out", genDir, "all"] -> do
      (templateName, size) <- parseTemplateDir genDir
      Just $ do
        templates <- getDirectoryFiles ("examples" </> "templates" </> templateName) ["*.sv.j2"]
        need [ "examples" </> "out" </> genDir </> dropExtension template | template <- templates ]
    _ -> Nothing

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
      (Timeout timeout)
      (FileStdout out)
      (FileStderr out)
      (AddEnv "OCAMLRUNPARAM" "b")
      "time" vera "compare" ("--solver=" ++ veraSolver) ("--dump-query=" ++ smtFile) left right
    end <- liftIO getCurrentTime
    case exitCode of
      ExitFailure 130 -> do
        liftIO $ appendFile out "Timed out"
        writeFile' timeFile "Timed out"
      ExitFailure err -> do
        liftIO $ appendFile out (printf "Failed with %d" err)
        writeFile' timeFile (printf "Failed (%d)" err)
      ExitSuccess -> writeFile' timeFile (show (diffUTCTime end begin))

  phony "vera" $ need [vera]
  vera %> \out -> do
    need =<< getDirectoryFiles "" ["vera//*.v", "vera//*.ml", "bin//*.ml", "bin//*.v"]
    cmd_ "dune" "build"

  -- Running eqy
  "//*.eqy.time" %> \out -> need [ out -<.> "log" ]
  "//*_vs_*/compare.eqy" %> \out -> do
    let template = "examples" </> "compare.eqy.j2"
        Just [dir, mod1, mod2] = filePattern "//*_vs_*/compare.eqy" out
    need [template]
    cmd_
      (Traced "jinja")
      (FileStdout out)
      "jinja2"
      "-D" ("SOLVER=" <> veraSolver)
      "-D" ("SV_GOLD=" <> (".." </> mod1 <.> "sv"))
      "-D" ("SV_GATE=" <> (".." </> mod2 <.> "sv"))
      template
  "//*_vs_*.eqy.log" %> \out -> do
    let Just [dir, mod1, mod2] = filePattern "//*_vs_*.eqy.log" out
        eqyDir = dropExtensions out
        eqyFile = eqyDir </> "compare.eqy"
        timeFile = out -<.> "time"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    need [eqyFile, left, right]
    begin <- liftIO getCurrentTime
    (Exit exitCode, Stdout output) <- cmd
      (Traced "eqy")
      (Timeout timeout)
      (FileStdout out)
      (FileStderr out)
      (Cwd eqyDir)
      "time" "eqy" "-f" "compare.eqy"
    end <- liftIO getCurrentTime
    case exitCode of
      ExitFailure 130 -> do
        liftIO $ appendFile out "Timed out"
        writeFile' timeFile "Timed out"
      ExitFailure err -> do
        let reason =
              if ("EQY ---- Keyboard interrupt or external termination signal ----" `isInfixOf` output)
              then "Timed out"
              else printf "Failed with %d" err
        liftIO $ appendFile out reason
        writeFile' timeFile reason
      ExitSuccess -> writeFile' timeFile (show (diffUTCTime end begin))

  phony "clean-run" $ do
    removeFilesAfter "examples/out"
      [ "//*.log", "//*.time", "//*.vera.smt2", "//*.csv", "//*.pdf" ]

  phony "plots" $ need ["examples/out/summary.pdf"]

  "examples/out/summary.pdf" %> \out -> do
    templateExampleDirs <- getDirectoryDirs ("examples" </> "templates")
    templateExamples <- fmap join <$> forM templateExampleDirs $ \exampleTemplateDir -> do
      moduleTemplates <- getDirectoryFiles ("examples" </> "templates" </> exampleTemplateDir) ["*.sv.j2"]
      let moduleNames = map dropExtensions moduleTemplates
      return
        [ printf "examples/out/%s/%s_vs_%s.summary.pdf" exampleTemplateDir left right
        | (left, right) <- allPairs moduleNames
        , left /= right
        ]
    need templateExamples
    cmd_ "gs" "-dBATCH" "-dNOPAUSE" "-q" "-sDEVICE=pdfwrite" ("-sOutputFile=" ++ out) templateExamples

  "examples/out/*/*.summary.pdf" %> \out -> do
    let Just [category, name] = filePattern "examples/out/*/*.summary.pdf" out
        base = dropExtensions out
        veraCsv = base <.> "vera.summary.csv"
        eqyCsv = base <.> "eqy.summary.csv"
        cleanName = map (\case '_' -> ' '; c -> c) (takeFileName name)
        title :: String = printf "%s - %s" category cleanName
    need [veraCsv, eqyCsv]
    (Exit code) <-
      cmd
        (Traced "gnuplot")
        "gnuplot" "-e"
        [ unwords
          [ "set terminal pdf;"
          , "set output '" ++ out ++ "';"
          , "set datafile separator ',';"
          , "set xlabel 'Bit width';"
          , "set ylabel 'Time (s)';"
          , "set title '" ++ title ++ "';"
          , "plot '" ++ veraCsv ++ "' using 1:2 with linespoints title 'vera'"
          , "   , '" ++ eqyCsv ++ "' using 1:2 with linespoints title 'eqy'"
          ] ]
    case code of
      ExitSuccess -> pure ()
      ExitFailure _ ->
        cmd_
          (Traced "gnuplot_dummy")
          "gnuplot" "-e"
          [ unwords
            [ "set terminal pdf;"
            , "set output '" ++ out ++ "';"
            , "set title '" ++ title ++ "';"
            , "unset border;"
            , "unset tics;"
            , "set xrange [0:1];"
            , "set yrange [0:1];"
            , "set label 1 'Error: Plot generation failed or missing data' at 0.5, 0.5 center font ',14';"
            , "plot NaN notitle"
            ]
          ]

  "examples/out/*/*_vs_*.*.summary.csv" %> \out -> do
    let Just [templateName, mod1, mod2, tool] = filePattern "examples/out/*/*_vs_*.*.summary.csv" out
        timeFiles = [ "examples/out"
                      </> (printf "gen_%s_%d" templateName w)
                      </> (printf "%s_vs_%s.%s.time" mod1 mod2 tool)
                    | w <- runSizes
                    ]
    times <- forP timeFiles readFile'
    writeFileLines out [ intercalate "," [show w, time] | (w, time) <- zip runSizes times ]

  "examples/out/summary.csv" %> \out -> do
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
    let examples = templateExamples
    let logFiles =
          [ "examples" </> "out" </> dir </> (left ++ "_vs_" ++ right ++ ".vera.log")
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
    writeFileLines out ("Example,Module1,Module2,Result,Time" :
      [ intercalate "," [dir, left, right, result, time]
      | ((dir, left, right), result, time) <- zip3 examples results times
      ])


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
templateForInstantiation (splitDirectories -> Snoc (Snoc (Snoc rest "out") dir) file) = do
  (category, size) <- parseTemplateDir dir
  Just (joinPath rest </> "templates" </> category </> file <> ".j2", size)
templateForInstantiation _ = Nothing

isTemplateInstantiation :: FilePath -> Bool
isTemplateInstantiation = isJust . templateForInstantiation

pattern Snoc :: [a] -> a -> [a]
pattern Snoc xs x <- (unsnoc -> Just (xs, x))

allPairs :: [a] -> [(a, a)]
allPairs [] = []
allPairs (x:xs) = map (x,) xs ++ allPairs xs
