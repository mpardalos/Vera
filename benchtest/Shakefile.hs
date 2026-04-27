#!/usr/bin/env runhaskell

{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util
import Data.Tuple (swap)
import Data.List (isSuffixOf, isInfixOf, isPrefixOf, stripPrefix, unsnoc, find, intercalate)
import Data.Bifunctor (bimap)
import Data.Char (isDigit)
import Data.Maybe (isJust, fromMaybe)
import Control.Monad (forM, forM_, guard, join, when, void)
import System.Directory qualified as SD
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Text.Printf (printf)
import System.Exit(ExitCode(..))
import Data.Function ((&))
import Debug.Trace
import Data.List.Extra (firstJust)
import Data.Functor ((<&>))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Data (Typeable)
import Data.Hashable (Hashable)
import Data.Binary (Binary)
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import System.Posix.Resource (setResourceLimit, getResourceLimit, Resource(ResourceOpenFiles), ResourceLimit(..), ResourceLimits(..))

-- | Path to vera binary
vera :: FilePath
vera = "../_build/install/default/bin/vera"

data ConfigRunSizes = ConfigRunSizes
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)
type instance RuleResult ConfigRunSizes = [Int]

data ConfigSolver = ConfigSolver
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)
type instance RuleResult ConfigSolver = String

data ConfigVeraMemoryLimit = ConfigVeraMemoryLimit
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)
type instance RuleResult ConfigVeraMemoryLimit = Int

data ConfigVeraTimeout = ConfigVeraTimeout
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)
type instance RuleResult ConfigVeraTimeout = Double

data ConfigYosysTimeout = ConfigYosysTimeout
  deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)
type instance RuleResult ConfigYosysTimeout = Double

data RunResult = RunResult
  { veraTime :: String
  , veraSolverTime :: String
  , eqyTime :: String
  }

main :: IO ()
main = shakeArgs shakeOptions {shakeThreads=0} $ do
  liftIO $ do
    -- Set open file soft limit to the hard limit
    ResourceLimits {hardLimit} <- getResourceLimit ResourceOpenFiles
    setResourceLimit ResourceOpenFiles (ResourceLimits hardLimit hardLimit)

  -- Sizes which templated examples will be evaluated at
  addOracle $ \ConfigRunSizes -> pure [4..8]
  -- Value of --solver= flag for vera
  addOracle $ \ConfigSolver -> pure "cvc5"
  -- Timeout for vera/eqy runs (in seconds)
  addOracle $ \ConfigVeraTimeout -> pure 10
  -- Vera memory limit (in bytes)
  addOracle $ \ConfigVeraMemoryLimit -> pure (1 * 1024 * 1024 * 1024) -- 1G
  -- Timeout for yosys synthesis (NOT symbiyosys/eqy equivalence checking)
  addOracle $ \ConfigYosysTimeout -> pure 600

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
    yosysTimeout <- askOracle ConfigYosysTimeout
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
  "//*_vs_*.vera.log" !%> \out [dir, mod1, mod2] -> do
    let smtFile = out -<.> "smt2"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    timeout <- askOracle ConfigVeraTimeout
    memoryLimit <- askOracle ConfigVeraMemoryLimit
    veraSolver <- askOracle ConfigSolver
    need [vera, left, right]
    (Exit veraExitCode, CmdTime veraTime) <- cmd
      (Traced "vera")
      (Timeout timeout)
      (FileStdout out)
      (FileStderr out)
      (AddEnv "OCAMLRUNPARAM" "b")
      (AddEnv "VERA_MAX_MEMORY" (show memoryLimit))
      vera "compare" ("--solver=none" ) ("--dump-query=" ++ smtFile) left right
    case veraExitCode of
      ExitFailure 130 -> liftIO $ do
        appendFile out "__time_vera: Vera timed out\n"
        appendFile out "__time_smt: Vera timed out\n"
      ExitFailure err -> liftIO $ do
        appendFile out (printf "__time_vera: Vera failed (%d)\n" err)
        appendFile out (printf "__time_smt: Vera failed (%d)\n" err)
      ExitSuccess -> do
        liftIO $ appendFile out (printf "__time_vera: %f\n" veraTime)
        (Exit smtExitCode, CmdTime smtTime, Stdouterr output) <- cmd
          (Traced (veraSolver ++ " for vera"))
          (Timeout timeout)
          veraSolver smtFile
        liftIO $ appendFile out ("\n" ++ output)
        case smtExitCode of
          ExitFailure 130 ->
            liftIO $ appendFile out "__time_smt: SMT Timed out\n"
          ExitFailure err -> do
            liftIO $ appendFile out (printf "__time_smt: SMT failed (%d)\n" err)
          ExitSuccess ->
            liftIO $ appendFile out (printf "__time_smt: %f\n" smtTime)

  phony "vera" $ need [vera]
  vera %> \out -> do
    need
      =<< getDirectoryFiles
        ""
        [ dir <//> ext
        | dir <- ["../vera", "../bin"],
          ext <- ["*.v", "*.ml"]
        ]
    cmd_ (Cwd "..") "dune" "build"

  -- Running eqy
  "//*_vs_*/compare.eqy" !%> \out [dir, mod1, mod2] -> do
    let template = "templates/compare.eqy.j2"
    need [template]
    solver <- askOracle ConfigSolver
    cmd_
      (Traced "jinja")
      (FileStdout out)
      "jinja2"
      "-D" ("SOLVER=" <> solver)
      "-D" ("SV_GOLD=" <> (".." </> mod1 <.> "sv"))
      "-D" ("SV_GATE=" <> (".." </> mod2 <.> "sv"))
      template
  "//*_vs_*.eqy.log" !%> \out [dir, mod1, mod2] -> do
    let eqyDir = dropExtensions out
        eqyFile = eqyDir </> "compare.eqy"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    timeout <- askOracle ConfigVeraTimeout
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

  "out/templates/*/*.summary.pdf" !%> \out [category, name] -> do
    let base = dropExtensions out
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

  let runEquivalenceCheckers dir modA modB = do
        veraOutput <- readFile' (dir </> (printf "%s_vs_%s.vera.log" modA modB))
        eqyOutput <- readFile' (dir </> (printf "%s_vs_%s.eqy.log" modA modB))
        let
           veraTime = findPrefixedLine "__time_vera: " veraOutput
           veraSolverTime = findPrefixedLine "__time_smt: " veraOutput
           eqyTime = findPrefixedLine "__time_eqy: " eqyOutput
        return RunResult { veraTime, veraSolverTime, eqyTime }

  "out/templates/*/*_vs_*.summary.csv" !%> \out [templateName, mod1, mod2] -> do
    runSizes <- askOracle ConfigRunSizes

    (times :: [(String, String)]) <- forP runSizes $ \size -> do
      RunResult { veraSolverTime, eqyTime } <- runEquivalenceCheckers
        ("out/templates" </> printf "gen_%s_%d" templateName size) mod1 mod2
      return (veraSolverTime, eqyTime)

    writeFileLines
      out
      ( ("Size,Vera,EQY")
          : [ intercalate "," [show w, veraTime, eqyTime]
            | (w, (veraTime, eqyTime)) <- zip runSizes times
            ]
      )

  -- EPFL benchmarks
  let
    blifToVerilog :: FilePath -> FilePath -> Action ()
    blifToVerilog from to = do
      need [ from ]
      let log = to <.> "log"
      cmd_ (FileStdout log) (FileStderr log) "yosys" "--commands" [ printf "read_blif %s; write_verilog %s" from to :: String ]
      trackWrite [to]

  -- | Rename the ports in the target file to match those in the source file
  let
    renamePorts :: FilePath -> FilePath -> Action ()
    renamePorts base target = do
        let portFilter = ".design.members[1].body.members[] | select(.kind == \"Port\") | .name"
        Stdout baseJson <- cmd "slang" "-q" "--ast-json=-" base
        Stdout basePorts <- cmd (Stdin baseJson) "jq" "-r" [portFilter]
        Stdout targetJson <- cmd "slang" "-q" "--ast-json=-" target
        Stdout targetPorts <- cmd (Stdin targetJson) "jq" "-r" [portFilter]
        -- The port we are renaming to needs to be escaped. This:
        --   a) Assumes that it is not already escaped in what we get from slang
        --   b) Adds a space afterwards so that the escaping doesn't "eat" any chars that happen to be after the identifier
        let portPairs = [ (printf "\\%s " basePort, targetPort)
                        | (basePort, targetPort) <- zip (lines basePorts) (lines targetPorts)
                        ]
        contents <- liftIO $ T.readFile target
        let contents' = foldl (\acc (to, from) -> T.replace (T.pack from) (T.pack to) acc) contents portPairs
        liftIO $ T.writeFile target contents'


  "out/EPFL-benchmarks/*/*/orig.sv" !%> \out [category, name] -> do
    let src = "EPFL-benchmarks" </> category </> name -<.> "v"
    copyFile' src out

  "out/EPFL-benchmarks/*/*/orig_blif.sv" !%> \out [category, name] -> do
    let base = "EPFL-benchmarks" </> category </> name -<.> "v"
    let src = "EPFL-benchmarks" </> category </> name -<.> "blif"
    blifToVerilog src out
    renamePorts base out

  "out/EPFL-benchmarks/*/*/best_size.sv" !%> \out [category, name] -> do
    let base = "EPFL-benchmarks" </> category </> name -<.> "v"
    [src] <- getDirectoryFiles "" [ printf "EPFL-benchmarks/best_results/size/%s_size_*.blif" name ]
    blifToVerilog src out
    renamePorts base out

  "out/EPFL-benchmarks/*/*/best_depth.sv" !%> \out [category, name] -> do
    let base = "EPFL-benchmarks" </> category </> name -<.> "v"
    [src] <- getDirectoryFiles "" [ printf "EPFL-benchmarks/best_results/depth/%s_depth_*.blif" name ]
    blifToVerilog src out
    renamePorts base out

  phony "clean-epfl" $ removeFilesAfter "out/EPFL-benchmarks" ["//"]

  phony "epfl" $ need ["out/EPFL-benchmarks/summary.csv" ]
  "out/EPFL-benchmarks/summary.csv" %> \out  -> do
    verilogFiles <- getDirectoryFiles "" [ "EPFL-benchmarks/arithmetic/*.v", "EPFL-benchmarks/random_control/*.v"]
    let targets =
         [ (category, name, "orig", target)
         | verilogFile <- verilogFiles
         , target <- ["orig_blif", "best_size", "best_depth"]
         , let Just [ category, name ] = filePattern "EPFL-benchmarks/*/*.v" verilogFile
         ]
    lines <- forP targets $ \(category, name, modA, modB) -> do
      let dir = "out/EPFL-benchmarks" </> category </> name
      RunResult { veraTime, veraSolverTime, eqyTime } <- runEquivalenceCheckers dir modA modB
      return (intercalate "," [category, name, modA, modB, veraTime, veraSolverTime, eqyTime])
    writeFile' out (unlines ( "Category,Name,A,B,Vera Time,Vera Solver time,EQY Time" : lines))


-- Helpers

-- | Like (%>), but you also get the list of matched components
(!%>) :: FilePath -> (FilePath -> [FilePath] -> Action ()) -> Rules ()
(!%>) pat act = pat %> \target ->
  let Just split = filePattern pat target
  in act target split

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

findPrefixedLine :: String -> String -> String
findPrefixedLine prefix =
  fromMaybe "Missing"
  . firstJust (stripPrefix prefix)
  . lines
