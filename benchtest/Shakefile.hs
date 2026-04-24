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
import Data.List.Extra (firstJust)
import Data.Functor ((<&>))

vera :: FilePath
vera = "../_build/install/default/bin/vera"

-- | Timeout for vera/eqy runs (in seconds)
timeout :: Double
timeout = 5

-- | Timeout for yosys synthesis (NOT symbiyosys/eqy equivalence checking)
yosysTimeout :: Double
yosysTimeout = 600

-- | Value of --solver= flag for vera
veraSolver :: String
-- veraSolver = "bitwuzla" -- Broken with symbiyosys
veraSolver = "cvc5"

-- | Sizes which templated examples will be evaluated at
runSizes :: [Int]
runSizes = [4..6]

tools :: [String]
tools = ["vera", "eqy"]

main :: IO ()
main = shakeArgs shakeOptions {shakeThreads=0} $ do
  phony "clean" $ do
    need ["clean-synth", "clean-run"]
    removeFilesAfter "" ["out/templates/summary.csv"]
    removeFilesAfter "out/templates" ["//"]

  phony "synth" $ do
    sources <- filter (not . (".synth.sv" `isSuffixOf`))
      <$> getDirectoryFiles "." ["templates//*.sv"]
    let targets = map (-<.> "synth.sv") sources
    need targets

  phony "clean-synth" $ do
    removeFilesAfter "out/" ["//*.synth.sv", "//*.synth.log"]

  -- Run yosys synthesis. Needs to take priority over the gen_ rule
  -- below, since they both match gen_*/*.synth.sv
  priority 2 $ "out//*.synth.sv" %> \out -> do
    let src = dropExtensions out <> ".sv"
    let log = dropExtensions out <> ".synth.log"
    need ["templates/synth.tcl", src]
    cmd_
      (Traced "yosys")
      (AddEnv "SV_INPUT" src)
      (AddEnv "SV_OUTPUT" out)
      (Timeout yosysTimeout)
      (FileStdout log)
      (FileStderr log)
      "yosys" "-c" "templates/synth.tcl"

  -- gen_<category>_<N>/<module>.sv -> templates/<category>/<module>.sv.j2
  "out/templates/gen_*/*.sv" %> \out -> do
    let Just (template, size) = templateForInstantiation out
        log = out -<.> "gen.log"
    need [template]
    cmd_
      (Traced "jinja")
      (FileStdout out)
      (FileStderr log)
      "jinja2" "-D" ("N=" <> show size) template

  -- Running vera
  "//*.vera.smt2" %> \out -> need [ out -<.> "log" ]
  "//*_vs_*.vera.log" %> \out -> do
    let Just [dir, mod1, mod2] = filePattern "//*_vs_*.vera.log" out
        smtFile = out -<.> "smt2"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    need [vera, left, right]
    (Exit veraExitCode, CmdTime veraTime) <- cmd
      (Traced "vera")
      (Timeout timeout)
      (FileStdout out)
      (FileStderr out)
      (AddEnv "OCAMLRUNPARAM" "b")
      vera "compare" ("--solver=none" ) ("--dump-query=" ++ smtFile) left right
    case veraExitCode of
      ExitFailure 130 -> liftIO $ do
        appendFile out "__time_vera: Vera timed out"
        appendFile out "__time_smt: Vera timed out"
      ExitFailure err -> liftIO $ do
        appendFile out (printf "__time_vera: Vera failed (%d)" err)
        appendFile out (printf "__time_smt: Vera failed (%d)" err)
      ExitSuccess -> do
        liftIO $ appendFile out (printf "__time_vera: %f" veraTime)
        (Exit smtExitCode, CmdTime smtTime, Stdouterr output) <- cmd
          (Traced (veraSolver ++ " for vera"))
          (Timeout timeout)
          veraSolver smtFile
        liftIO $ appendFile out ("\n" ++ output)
        case smtExitCode of
          ExitFailure 130 ->
            liftIO $ appendFile out "__time_smt: SMT Timed out"
          ExitFailure err -> do
            liftIO $ appendFile out (printf "__time_smt: SMT failed (%d)" err)
          ExitSuccess ->
            liftIO $ appendFile out (printf "__time_smt: %f" smtTime)

  phony "vera" $ need [vera]
  vera %> \out -> do
    need
      =<< getDirectoryFiles
        ""
        [ dir <//> ext
        | dir <- ["../vera", "../bin"],
          ext <- ["*.v", "*.ml"]
        ]
    cmd_ "dune" "build"

  -- Running eqy
  "//*_vs_*/compare.eqy" %> \out -> do
    let template = "templates/compare.eqy.j2"
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
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    need [eqyFile, left, right]
    (Exit exitCode, Stdout output, CmdTime eqyTime) <- cmd
      (Traced "eqy")
      (Timeout timeout)
      (FileStdout out)
      (FileStderr out)
      (Cwd eqyDir)
      "eqy" "-f" "compare.eqy"
    case exitCode of
      ExitFailure 130 -> do
        liftIO $ appendFile out "__time_eqy: Timed out"
      ExitFailure err -> do
        let reason =
              if ("EQY ---- Keyboard interrupt or external termination signal ----" `isInfixOf` output)
              then "Timed out"
              else printf "Failed with %d" err
        liftIO $ appendFile out (printf "__time_eqy: %s" reason)
      ExitSuccess ->
        liftIO $ appendFile out (printf "__time_eqy: %f" eqyTime)

  phony "clean-run" $ do
    removeFilesAfter "out/templates"
      [ "//*.log", "//*.time", "//*.vera.smt2", "//*.csv", "//*.pdf" ]

  phony "plots" $ need ["out/templates/summary.pdf"]

  "out/templates/summary.pdf" %> \out -> do
    templateExampleDirs <- getDirectoryDirs ("templates")
    templateExamples <- fmap join <$> forM templateExampleDirs $ \exampleTemplateDir -> do
      moduleTemplates <- getDirectoryFiles ("templates" </> exampleTemplateDir) ["*.sv.j2"]
      let moduleNames = map dropExtensions moduleTemplates
      return
        [ printf "out/templates/%s/%s_vs_%s.summary.pdf" exampleTemplateDir left right
        | (left, right) <- allPairs moduleNames
        , left /= right
        ]
    need templateExamples
    cmd_ "gs" "-dBATCH" "-dNOPAUSE" "-q" "-sDEVICE=pdfwrite" ("-sOutputFile=" ++ out) templateExamples

  "out/templates/*/*.summary.pdf" %> \out -> do
    let Just [category, name] = filePattern "out/templates/*/*.summary.pdf" out
        base = dropExtensions out
        summaryCSV = base <.> "summary.csv"
        cleanName = map (\case '_' -> ' '; c -> c) (takeFileName name)
        title :: String = printf "%s - %s" category cleanName
    need [summaryCSV]
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
          , "set xtics 1;"
          , "plot '" ++ summaryCSV ++ "' using 1:2 with linespoints title columnheader(2)"
          , "   , '" ++ summaryCSV ++ "' using 1:3 with linespoints title columnheader(3)"
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

  "out/templates/*/*_vs_*.summary.csv" %> \out -> do
    let Just [templateName, mod1, mod2] = filePattern "out/templates/*/*_vs_*.summary.csv" out

    -- [(vera time, eqy time)]
    (times :: [(String, String)]) <- forP runSizes $ \size -> do
      veraLog <- readFile' $
        "out/templates" </> (printf "gen_%s_%d" templateName size) </> (printf "%s_vs_%s.vera.log" mod1 mod2)
      let veraTime = veraLog & lines & firstJust (stripPrefix "__time_smt: ") & fromMaybe "Missing"
      eqyLog <- readFile' $
        "out/templates" </> (printf "gen_%s_%d" templateName size) </> (printf "%s_vs_%s.eqy.log" mod1 mod2)
      let eqyTime = eqyLog & lines & firstJust (stripPrefix "__time_eqy: ") & fromMaybe "Missing"
      return (veraTime, eqyTime)
  
    writeFileLines
      out
      ( ("Size,Vera,EQY")
          : [ intercalate "," [show w, veraTime, eqyTime]
            | (w, (veraTime, eqyTime)) <- zip runSizes times
            ]
      )

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
templateForInstantiation (splitDirectories -> ["out", "templates", dir, file]) = do
  (category, size) <- parseTemplateDir dir
  Just ("templates" </> category </> file <> ".j2", size)
templateForInstantiation _ = Nothing

isTemplateInstantiation :: FilePath -> Bool
isTemplateInstantiation = isJust . templateForInstantiation

pattern Snoc :: [a] -> a -> [a]
pattern Snoc xs x <- (unsnoc -> Just (xs, x))

allPairs :: [a] -> [(a, a)]
allPairs [] = []
allPairs (x:xs) = map (x,) xs ++ allPairs xs
