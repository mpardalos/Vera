#!/usr/bin/env runhaskell

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}

import Control.DeepSeq (NFData)
import Control.Monad (forM, forM_, guard, join, void, when)
import Data.Bifunctor (bimap)
import Data.Binary (Binary)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BS8
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Char (isDigit)
import Data.Data (Typeable)
import Data.Function ((&))
import Data.Functor ((<&>))
import Data.Hashable (Hashable)
import Data.List (find, intercalate, isInfixOf, isPrefixOf, isSuffixOf, sort, stripPrefix, unsnoc)
import Data.List.Extra (firstJust)
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Text.IO qualified as T
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Tuple (swap)
import Debug.Trace
import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util
import GHC.Generics (Generic)
import System.Directory qualified as SD
import System.Exit (ExitCode (..))
import System.Posix.Resource (Resource (ResourceOpenFiles), ResourceLimit (..), ResourceLimits (..), getResourceLimit, setResourceLimit)
import Text.Printf (printf)
import Safe (fromJustNote, readMay)

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
  { time :: Text
  , result :: Text
  }

data BenchmarkResult = BenchmarkResult
  { size :: Int
  , vera :: RunResult
  , veraSolver :: RunResult
  , eqy :: RunResult
  }

main :: IO ()
main = shakeArgs shakeOptions{shakeThreads = 0} $ do
  liftIO $ do
    -- Set open file soft limit to the hard limit
    ResourceLimits{hardLimit} <- getResourceLimit ResourceOpenFiles
    setResourceLimit ResourceOpenFiles (ResourceLimits hardLimit hardLimit)

  -- Sizes which templated examples will be evaluated at
  addOracle $ \ConfigRunSizes -> pure [4 .. 8]
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
    sources <-
      filter (not . (".synth.sv" `isSuffixOf`))
        <$> getDirectoryFiles "." ["templates//*.sv"]
    let targets = map (-<.> "synth.sv") sources
    need targets

  phony "clean-synth" $ do
    removeFilesAfter "out/" ["//*.synth.sv", "//*.synth.log"]

  -- Run yosys synthesis. Needs to take priority over the gen_ rule
  -- below, since they both match gen_*/*.synth.sv
  priority 2 $
    "out//*.synth.sv" %> \out -> do
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
        "yosys"
        "-c"
        "templates/synth.tcl"

  -- gen_<category>_<N>/<module>.sv -> templates/<category>/<module>.sv.j2
  "out/templates/gen_*/*.sv" %> \out -> do
    let Just (template, size) = templateForInstantiation out
        log = out -<.> "gen.log"
    need [template]
    cmd_
      (Traced "jinja")
      (FileStdout out)
      (FileStderr log)
      "jinja2"
      "-D"
      ("N=" <> show size)
      template

  -- Running vera
  "//*.vera.smt2" %> \out -> need [out -<.> "log"]
  "//*_vs_*.vera.log" !%> \out [dir, mod1, mod2] -> do
    let smtFile = out -<.> "smt2"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    timeout <- askOracle ConfigVeraTimeout
    memoryLimit <- askOracle ConfigVeraMemoryLimit
    veraSolver <- askOracle ConfigSolver
    need [vera, left, right]
    (Exit veraExitCode, CmdTime veraTime) <-
      cmd
        (Traced "vera")
        (Timeout timeout)
        (FileStdout out)
        (FileStderr out)
        (AddEnv "OCAMLRUNPARAM" "b")
        (AddEnv "VERA_MAX_MEMORY" (show memoryLimit))
        vera
        "compare"
        ("--solver=none")
        ("--dump-query=" ++ smtFile)
        left
        right
    liftIO $ appendFile out (printf "__time_vera: %.2f\n" veraTime)
    case veraExitCode of
      ExitFailure (-2) -> liftIO $ do
        appendFile out "__result_vera: Timeout\n"
      ExitFailure err -> liftIO $ do
        appendFile out (printf "__result_vera: failed (%d)\n" err)
      ExitSuccess -> do
        liftIO $ appendFile out "__result_vera: OK\n"
        (Exit smtExitCode, CmdTime smtTime, Stdouterr output) <-
          cmd
            (Traced (veraSolver ++ " for vera"))
            (Timeout timeout)
            veraSolver
            smtFile
        liftIO $ appendFile out ("\n" ++ output)
        liftIO $ appendFile out (printf "__time_smt: %.2f\n" smtTime)
        case smtExitCode of
          ExitFailure 130 ->
            liftIO $ appendFile out "__result_smt: Timeout\n"
          ExitFailure err -> do
            liftIO $ appendFile out (printf "__result_smt: failed (%d)\n" err)
          ExitSuccess ->
            if "unsat" `isInfixOf` output
              then liftIO $ appendFile out "__result_smt: OK\n"
              else liftIO $ appendFile out "__result_smt: Incorrect result\n"

  phony "vera" $ need [vera]
  vera %> \out -> do
    need
      =<< getDirectoryFiles
        ""
        [ dir <//> ext
        | dir <- ["../vera", "../bin"]
        , ext <- ["*.v", "*.ml"]
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
      "-D"
      ("SOLVER=" <> solver)
      "-D"
      ("SV_GOLD=" <> (".." </> mod1 <.> "sv"))
      "-D"
      ("SV_GATE=" <> (".." </> mod2 <.> "sv"))
      template
  "//*_vs_*.eqy.log" !%> \out [dir, mod1, mod2] -> do
    let eqyDir = dropExtensions out
        eqyFile = eqyDir </> "compare.eqy"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    timeout <- askOracle ConfigVeraTimeout
    need [eqyFile, left, right]
    (Exit exitCode, Stdout output, CmdTime eqyTime) <-
      cmd
        (Traced "eqy")
        (Timeout timeout)
        (FileStdout out)
        (FileStderr out)
        (Cwd eqyDir)
        "eqy"
        "-f"
        "compare.eqy"
    liftIO $ appendFile out (printf "__time_eqy: %.2f\n" eqyTime)
    case exitCode of
      ExitFailure 130 -> do
        liftIO $ appendFile out "__result_eqy: Timeout\n"
      ExitFailure err
        | "EQY ---- Keyboard interrupt or external termination signal ----" `isInfixOf` output ->
            liftIO $ appendFile out "__result_eqy: Timeout\n"
        | otherwise ->
            liftIO $ appendFile out (printf "__result_eqy: Failed (%d)\n" err)
      ExitSuccess ->
        liftIO $ appendFile out "__result_eqy: OK\n"

  phony "clean-run" $ do
    removeFilesAfter
      "out/templates"
      ["//*.log", "//*.time", "//*.vera.smt2", "//*.csv", "//*.pdf"]

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
        "gnuplot"
        "-e"
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
            ]
        ]
    case code of
      ExitSuccess -> pure ()
      ExitFailure _ ->
        cmd_
          (Traced "gnuplot_dummy")
          "gnuplot"
          "-e"
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
        let genALogFile = dir </> (printf "%s.sv.log" modA)
        let genBLogFile = dir </> (printf "%s.sv.log" modB)
        let veraLogFile = dir </> (printf "%s_vs_%s.vera.log" modA modB)
        let eqyLogFile = dir </> (printf "%s_vs_%s.eqy.log" modA modB)
        need [genALogFile, genBLogFile, veraLogFile, eqyLogFile]
        aSize <- readDesignSize <$> liftIO (T.readFile genALogFile)
        bSize <- readDesignSize <$> liftIO (T.readFile genBLogFile)

        veraOutput <- liftIO $ T.readFile veraLogFile
        eqyOutput <- liftIO $ T.readFile eqyLogFile
        return
          BenchmarkResult
            { size = aSize + bSize
            , vera =
                RunResult
                  { time = findPrefixedLine (T.pack "__time_vera: ") veraOutput
                  , result = findPrefixedLine (T.pack "__result_vera: ") veraOutput
                  }
            , veraSolver =
                RunResult
                  { time = findPrefixedLine (T.pack "__time_smt: ") veraOutput
                  , result = findPrefixedLine (T.pack "__result_smt: ") veraOutput
                  }
            , eqy =
                RunResult
                  { time = findPrefixedLine (T.pack "__time_eqy: ") eqyOutput
                  , result = findPrefixedLine (T.pack "__result_eqy: ") eqyOutput
                  }
            }

  -- EPFL benchmarks
  let
    blifToVerilog :: FilePath -> FilePath -> Action ()
    blifToVerilog from to = do
      need [from]
      let log = to <.> "log"
      -- rename -hide gives the internal wires of the module private
      -- names. This prevents eqy from trying to match them up with
      -- wires in the other module that this will be compared to.
      -- These private names are something like `_0793_`, which
      -- doesn't look globally unique, so I'm not sure this will work
      -- if it is run on both this and the orig that this is compared
      -- to, so we only run the rename here (on the blif), and not on
      -- the orig file. If we compare two Verilogs which both come
      -- from blifs from this function, there might be trouble.
      cmd_
        (FileStdout log)
        (FileStderr log)
        "yosys"
        "--commands"
        [printf "read_blif %s; rename -hide *; write_verilog %s; stat" from to :: String]
      trackWrite [to]

  -- \| Rename the ports in the target file to match those in the source file
  let
    renamePorts :: FilePath -> FilePath -> Action ()
    renamePorts base target = do
      let portFilter = ".design.members[1].body.members[] | select(.kind == \"Port\") | .name"
      Stdout (basePortsLines :: ByteString) <- cmd Shell (printf "slang -q --ast-json=- %s | jq -r '%s'" base portFilter :: String)
      Stdout (targetPortsLines :: ByteString) <- cmd Shell (printf "slang -q --ast-json=- %s | jq -r '%s'" target portFilter :: String)
      let basePorts :: [ByteString] = BS8.lines basePortsLines
      let targetPorts :: [ByteString] = BS8.lines targetPortsLines
      if (sort basePorts /= sort targetPorts)
        then do
          -- The port we are renaming to needs to be escaped. This:
          --   a) Assumes that it is not already escaped in what we get from slang
          --   b) Adds a space afterwards so that the escaping doesn't "eat" any chars that happen to be after the identifier
          let portPairs =
                [ (BS8.pack "\\\\" <> basePort <> BS8.pack " ", targetPort)
                | (basePort, targetPort) <- zip basePorts targetPorts
                ]
          let sedScript = BS8.unlines [BS8.pack "s/\\<" <> from <> BS8.pack "\\>/" <> to <> BS8.pack "/g" | (to, from) <- portPairs]
          liftIO $ BS.writeFile (target <.> "sed") sedScript
          cmd_ "sed" ["-i", "-f", target <.> "sed", target]
          liftIO $ T.appendFile target (T.pack "\n// PORTS RENAMED\n")
        else liftIO $ T.appendFile target (T.pack "\n// PORTS NOT RENAMED\n")

  "out/EPFL-benchmarks/*/*/orig.sv" !%> \out [category, name] -> do
    let src = "EPFL-benchmarks" </> category </> name -<.> "v"
    copyFile' src out

  -- For the ones that come from blifs, the blifToVerilog generates a
  -- log. For the originals, we need to run yosys
  "out/EPFL-benchmarks//*.sv.log" %> \out -> need [dropExtension out]
  priority 2 $ do
    "out/EPFL-benchmarks/*/*/orig.sv.log" !%> \out [category, name] -> do
      let svFile = "out/EPFL-benchmarks" </> category </> name </> "orig.sv"
      need [svFile]
      cmd_
        (FileStdout out)
        (FileStderr out)
        "yosys"
        "--commands"
        [printf "read_verilog -sv %s; stat" svFile :: String]

  "out/EPFL-benchmarks/*/*/orig_blif.sv" !%> \out [category, name] -> do
    let base = "EPFL-benchmarks" </> category </> name -<.> "v"
    let src = "EPFL-benchmarks" </> category </> name -<.> "blif"
    blifToVerilog src out
    renamePorts base out

  "out/EPFL-benchmarks/*/*/best_size.sv" !%> \out [category, name] -> do
    let base = "EPFL-benchmarks" </> category </> name -<.> "v"
    [src] <- getDirectoryFiles "" [printf "EPFL-benchmarks/best_results/size/%s_size_*.blif" name]
    blifToVerilog src out
    renamePorts base out

  "out/EPFL-benchmarks/*/*/best_depth.sv" !%> \out [category, name] -> do
    let base = "EPFL-benchmarks" </> category </> name -<.> "v"
    [src] <- getDirectoryFiles "" [printf "EPFL-benchmarks/best_results/depth/%s_depth_*.blif" name]
    blifToVerilog src out
    renamePorts base out

  phony "clean-epfl" $ removeFilesAfter "out/EPFL-benchmarks" ["//"]

  phony "epfl" $ need ["out/EPFL-benchmarks/summary.csv"]
  "out/EPFL-benchmarks/summary.csv" %> \out -> do
    verilogFiles <- getDirectoryFiles "" ["EPFL-benchmarks/arithmetic/*.v", "EPFL-benchmarks/random_control/*.v"]
    let targets =
          [ (category, name, "orig", target)
          | verilogFile <- verilogFiles
          , target <- ["orig_blif", "best_size", "best_depth"]
          , let Just [category, name] = filePattern "EPFL-benchmarks/*/*.v" verilogFile
          ]
    lines <- forP targets $ \(category, name, modA, modB) -> do
      let dir = "out/EPFL-benchmarks" </> category </> name
      result <- runEquivalenceCheckers dir modA modB
      return
        ( T.intercalate
            (T.pack ",")
            [ T.pack category
            , T.pack name
            , T.pack modA
            , T.pack modB
            , T.show result.size
            , result.vera.result
            , result.vera.time
            , result.veraSolver.result
            , result.veraSolver.time
            , result.eqy.result
            , result.eqy.time
            ]
        )
    liftIO $
      T.writeFile
        out
        ( T.unlines
            ( T.pack "Category,Name,A,B,Size,Vera Result,Vera time,Vera solver result,Vera solver time,EQY result,EQY time"
                : lines
            )
        )

-- Helpers

-- | Like (%>), but you also get the list of matched components
(!%>) :: FilePath -> (FilePath -> [FilePath] -> Action ()) -> Rules ()
(!%>) pat act =
  pat %> \target ->
    let Just split = filePattern pat target
     in act target split

-- Split the list on the first instance of the separator
splitOn :: (Eq a) => a -> [a] -> ([a], [a])
splitOn p lst =
  ( takeWhile (/= p) $ lst
  , tailSafe . dropWhile (/= p) $ lst
  )
 where
  tailSafe [] = []
  tailSafe (x : xs) = xs

-- Split the list on the last instance of the separator
splitOnLast :: (Eq a) => a -> [a] -> ([a], [a])
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
allPairs (x : xs) = map (x,) xs ++ allPairs xs

findPrefixedLine :: Text -> Text -> Text
findPrefixedLine prefix =
  fromMaybe (T.pack "-")
    . firstJust (T.stripPrefix prefix)
    . T.lines

-- Read design size out of a yosys log with the `stat` command
readDesignSize :: Text -> Int
readDesignSize txt =
  txt
  & T.lines
  & map T.strip
  & map T.words
  & map (map T.unpack)
  & firstJust (\case
                  [readMay -> Just count, "wire", "bits"] -> Just count
                  _ -> Nothing
                  )
  & fromMaybe (-1)
