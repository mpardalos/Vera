#!/usr/bin/env runhaskell

{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoFieldSelectors #-}

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
import Data.Csv
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
import Data.Text.IO.Utf8 qualified as T
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import Data.Tuple (swap)
import Debug.Trace
import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util
import GHC.Generics (Generic)
import Language.Haskell.TH.Syntax (Exp (LitE), Lit (StringL), loc_filename, location)
import Safe (fromJustNote, readMay)
import System.Directory qualified as SD
import System.Exit (ExitCode (..))
import System.Posix.Resource (Resource (ResourceOpenFiles), ResourceLimit (..), ResourceLimits (..), getResourceLimit, setResourceLimit)
import Text.Printf (printf)

{- | Directory containing this Shakefile, captured at compile time. All the
paths in this file are relative to it, so we @cd@ here at startup and the
build can then be run from any working directory.
-}
shakefileDir :: FilePath
shakefileDir = takeDirectory $(location >>= \l -> pure (LitE (StringL (loc_filename l))))

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

data YosysGateCount = YosysGateCount FilePath
    deriving (Show, Typeable, Eq, Generic, Hashable, Binary, NFData)

type instance RuleResult YosysGateCount = Int

data RunResult = RunResult
    { time :: Text
    , result :: Text
    }

{- | Named fields for one run, prefixed so that the several runs in a
'BenchmarkResult' do not collide. E.g. @prefix = "Vera"@ gives the columns
@Vera Result@ and @Vera Time@.
-}
runResultFields :: ByteString -> (ByteString, ByteString)
runResultFields prefix = (prefix <> BS8.pack " Result", prefix <> BS8.pack " Time")

runResultHeader :: ByteString -> Header
runResultHeader (runResultFields -> (resultField, timeField)) =
    header [resultField, timeField]

runResultToNamedRecord :: ByteString -> RunResult -> NamedRecord
runResultToNamedRecord (runResultFields -> (resultField, timeField)) r =
    namedRecord [resultField .= r.result, timeField .= r.time]

parseRunResult :: ByteString -> NamedRecord -> Parser RunResult
parseRunResult (runResultFields -> (resultField, timeField)) m = do
    result <- m .: resultField
    time <- m .: timeField
    pure RunResult{time, result}

gibiBytes :: Int -> Int
gibiBytes = (1024 * 1024 * 1024 *)

{- | How much memory we estimate slang to maximally use, in gigabytes.
Not enforced, just an estimate
-}
slangMemory :: Int
slangMemory = 1

{- | How much memory we estimate yosys to maximally use, in gigabytes.
Not enforced, just an estimate
-}
yosysMemory :: Int
yosysMemory = 1

{- | How much memory we estimate eqy to maximally use, in gigabytes.
Not enforced, just an estimate
-}
eqyMemory :: Int
eqyMemory = 4

getPorts :: Maybe String -> FilePath -> IO [ByteString]
getPorts direction modulePath = do
    let dirFilter = case direction of
            Nothing -> "true"
            Just dir -> printf ".direction == \"%s\"" dir
    let portFilter :: String = printf ".design.members[1].body.members[] | select(.kind == \"Port\" and %s) | .name" dirFilter
    Stdout (basePortsLines :: ByteString) <-
        cmd Shell (printf "slang -q --ast-json=- %s | jq -r '%s'" modulePath portFilter :: String)
    return (BS8.lines basePortsLines)

getAllPorts, getInputs, getOutputs :: FilePath -> IO [ByteString]
getAllPorts = getPorts Nothing
getInputs = getPorts (Just "In")
getOutputs = getPorts (Just "Out")

data Benchmark = MkBenchmark
    { baseDir :: FilePath
    , modA :: String
    , modB :: String
    }

data BenchmarkResult = MkBenchmarkResult
    { benchmark :: Benchmark
    , size :: Int
    , veraRun :: RunResult
    , veraSMTRun :: RunResult
    , eqyRun :: RunResult
    }

designField, modAField, modBField, sizeField :: ByteString
designField = BS8.pack "Design"
modAField = BS8.pack "A"
modBField = BS8.pack "B"
sizeField = BS8.pack "Size"

veraPrefix, smtPrefix, eqyPrefix :: ByteString
veraPrefix = BS8.pack "Vera"
smtPrefix = BS8.pack "SMT"
eqyPrefix = BS8.pack "EQY"

instance ToNamedRecord Benchmark where
    toNamedRecord b =
        namedRecord
            [ designField .= b.baseDir
            , modAField .= b.modA
            , modBField .= b.modB
            ]

instance FromNamedRecord Benchmark where
    parseNamedRecord m =
        MkBenchmark <$> m .: designField <*> m .: modAField <*> m .: modBField

instance DefaultOrdered Benchmark where
    headerOrder _ = header [designField, modAField, modBField]

instance ToNamedRecord BenchmarkResult where
    toNamedRecord r =
        mconcat
            [ toNamedRecord r.benchmark
            , namedRecord [sizeField .= r.size]
            , runResultToNamedRecord veraPrefix r.veraRun
            , runResultToNamedRecord smtPrefix r.veraSMTRun
            , runResultToNamedRecord eqyPrefix r.eqyRun
            ]

instance FromNamedRecord BenchmarkResult where
    parseNamedRecord m = do
        benchmark <- parseNamedRecord m
        size <- m .: sizeField
        veraRun <- parseRunResult veraPrefix m
        veraSMTRun <- parseRunResult smtPrefix m
        eqyRun <- parseRunResult eqyPrefix m
        pure MkBenchmarkResult{benchmark, size, veraRun, veraSMTRun, eqyRun}

instance DefaultOrdered BenchmarkResult where
    headerOrder _ =
        mconcat
            [ headerOrder (undefined :: Benchmark)
            , header [sizeField]
            , runResultHeader veraPrefix
            , runResultHeader smtPrefix
            , runResultHeader eqyPrefix
            ]

main :: IO ()
main = shakeArgs shakeOptions{shakeThreads = 0} $ do
    --- SETTINGS ---------------------------------------------
    -- Total memory on the machine in GB. Used to limit parallelism. Must be
    -- higher than ConfigVeraMemoryLimit below
    memResource <- newResource "RAM GB" 256
    -- Solver used by both Vera and eqy. The artifact environment allows
    -- for "cvc5" or "z3". "Bitwuzla" was attempted too but appears to
    -- be buggy for this version of EQY.
    addOracle $ \ConfigSolver -> pure "cvc5"
    -- Timeout for vera/eqy runs (in seconds)
    addOracle $ \ConfigVeraTimeout -> pure 300
    -- Vera memory limit (in GB)
    addOracle $ \ConfigVeraMemoryLimit -> pure 32
    ----------------------------------------------------------

    -- The following are only relevant for the templated tests, which
    -- are not part of the evaluation on the paper. These make no
    -- difference for the EPFL benchmarks

    -- Sizes which templated examples will be evaluated at
    addOracle $ \ConfigRunSizes -> pure [4 .. 8]
    -- Timeout for yosys synthesis (in)(NOT symbiyosys/eqy equivalence checking)
    addOracle $ \ConfigYosysTimeout -> pure 600

    liftIO $ do
        -- Set open file soft limit to the hard limit
        ResourceLimits{hardLimit} <- getResourceLimit ResourceOpenFiles
        setResourceLimit ResourceOpenFiles (ResourceLimits hardLimit hardLimit)

        -- Make all relative paths below resolve against the Shakefile's directory,
        -- regardless of where the build is invoked from. makeAbsolute runs before we
        -- change directory, so a relative shakefileDir resolves against the original
        -- working directory.
        SD.setCurrentDirectory =<< SD.makeAbsolute shakefileDir

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

    qYosysGateCount <- addOracleCache $ \(YosysGateCount verilogFile) -> do
        Stdout (output :: ByteString) <-
            cmd "yosys" "--commands" [printf "read_verilog -sv %s; stat" verilogFile :: String]
        return $
            output
                & BS8.lines
                & map BS8.strip
                & map BS8.words
                & map (map BS8.unpack)
                & firstJust (\case [readMay -> Just count, "wire", "bits"] -> Just count; _ -> Nothing)
                & fromMaybe (-1)
    let getDesignSize fp = qYosysGateCount (YosysGateCount fp)

    -- Run yosys synthesis. Needs to take priority over the gen_ rule
    -- below, since they both match gen_*/*.synth.sv
    priority 2 $
        "out//*.synth.sv" %> \out -> do
            let src = dropExtensions out <> ".sv"
            let log = dropExtensions out <> ".synth.log"
            need ["templates/synth.tcl", src]
            yosysTimeout <- askOracle ConfigYosysTimeout
            withResource memResource yosysMemory $
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
        veraMemoryLimit <- askOracle ConfigVeraMemoryLimit
        veraSolver <- askOracle ConfigSolver
        need [vera, left, right]
        (Exit veraExitCode, CmdTime veraTime) <-
            withResource memResource veraMemoryLimit $
                cmd
                    (Traced "vera")
                    (Timeout timeout)
                    (FileStdout out)
                    (FileStderr out)
                    (AddEnv "OCAMLRUNPARAM" "b")
                    (AddEnv "VERA_MAX_MEMORY" (show (gibiBytes veraMemoryLimit)))
                    (AddEnv "VERA_TRACE" "1")
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
                    withResource memResource veraMemoryLimit $
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
                        let result =
                                case output & T.pack & T.lines & last & T.strip & T.unpack of
                                    "unsat" -> "OK"
                                    "sat" -> "False negative"
                                    _ -> "Error"
                         in liftIO $ appendFile out ("__result_smt: " ++ result ++ "\n")

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
        outputs <- liftIO $ getOutputs (dir </> mod1 <.> "sv")
        let outputsJson =
                "[" ++ intercalate "," ["\"" ++ BS8.unpack output ++ "\"" | output <- outputs] ++ "]"
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
            (Stdin ("{\"OUTPUTS\":" ++ outputsJson ++ "}"))
            "--format=json"
            template
            "-"

    "//*_vs_*.eqy.log" !%> \out [dir, mod1, mod2] -> do
        let eqyDir = dropExtensions out
            eqyFile = eqyDir </> "compare.eqy"
            left = dir </> mod1 <.> "sv"
            right = dir </> mod2 <.> "sv"
        timeout <- askOracle ConfigVeraTimeout
        need [eqyFile, left, right]
        (Exit exitCode, Stdout output, CmdTime eqyTime) <-
            withResource memResource eqyMemory $
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

    let readVeraLog :: Text -> (RunResult, RunResult)
        readVeraLog log =
            ( RunResult
                { time = findPrefixedLine (T.pack "__time_vera: ") log
                , result = findPrefixedLine (T.pack "__result_vera: ") log
                }
            , RunResult
                { time = findPrefixedLine (T.pack "__time_smt: ") log
                , result = findPrefixedLine (T.pack "__result_smt: ") log
                }
            )

    let readEqyLog :: Text -> RunResult
        readEqyLog log =
            RunResult
                { time = findPrefixedLine (T.pack "__time_eqy: ") log
                , result = findPrefixedLine (T.pack "__result_eqy: ") log
                }

    let runBenchmarks :: [Benchmark] -> Action [BenchmarkResult]
        runBenchmarks benchmarks = do
            let veraLog b = b.baseDir </> printf "%s_vs_%s.vera.log" b.modA b.modB
            let eqyLog b = b.baseDir </> printf "%s_vs_%s.eqy.log" b.modA b.modB
            need $ [veraLog, eqyLog] <*> benchmarks
            forM benchmarks $ \b -> do
                (veraRun, veraSMTRun) <- readVeraLog <$> liftIO (T.readFile (veraLog b))
                eqyRun <- readEqyLog <$> liftIO (T.readFile (eqyLog b))
                (sizeA, sizeB) <-
                    getDesignSize (b.baseDir </> b.modA <.> "sv")
                        `par` getDesignSize (b.baseDir </> b.modB <.> "sv")
                pure MkBenchmarkResult{benchmark = b, size = sizeA + sizeB, veraRun, veraSMTRun, eqyRun}

    let benchmarksReport :: FilePath -> [Benchmark] -> Action ()
        benchmarksReport out benchmarks = do
            results <- runBenchmarks benchmarks
            -- encodeDefaultOrderedByName writes the header itself. The
            -- non-default line ending keeps the file plain-\n, as before.
            let csv = encodeDefaultOrderedByNameWith defaultEncodeOptions{encUseCrLf = False} results
            liftIO (LBS.writeFile out csv)
            trackWrite [out]

    -- EPFL benchmarks
    let blifToVerilog :: FilePath -> FilePath -> Action ()
        blifToVerilog from to = do
            need [from]
            let log = to <.> "log"
            cmd_
                (FileStdout log)
                (FileStderr log)
                "yosys"
                "--commands"
                [printf "read_blif %s; write_verilog %s" from to :: String]
            trackWrite [to]

    -- \| Rename the ports in the target file to match those in the source file
    let renamePorts :: FilePath -> FilePath -> Action ()
        renamePorts base target = do
            (basePorts, targetPorts) <- liftIO (getAllPorts base) `par` liftIO (getAllPorts target)
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

    "out/EPFL-benchmarks/*/*/orig_blif.sv" !%> \out [category, name] -> do
        let base = "EPFL-benchmarks" </> category </> name -<.> "v"
        let src = "EPFL-benchmarks" </> category </> name -<.> "blif"

        -- This is a dirty hack.
        --
        -- When we convert from blif to verilog using yosys, we don't have
        -- control over the order of ports in the resulting Verilog. It
        -- just so happens that in every benchmark except this specific
        -- one, we get an order which matches the original Verilog.  For
        -- this specific benchmark, we get the wrong order: The "F"
        -- output, which is last in the original Verilog, gets put last in
        -- the converted blif. I tried fixing this by changing the order
        -- that ports are declared in the blif, but that had no effect.
        --
        -- To counteract this, we rename the ports in the blif to match
        -- the names that they have in the best_size and best_depth
        -- versions, which we know give the correct order. Note: These
        -- names are renamed AGAIN in the renamePorts pass below.
        when ((category, name) == ("random_control", "priority")) $ do
            cmd_ "sed" "-i" "-E" "-e" "s/P\\[([0-9]+)\\]/po\\1/g" "-e" "s/\\bF\\b/po7/g" src

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

    let mkEPFLBenchmarks :: [(String, String)] -> [Benchmark]
        mkEPFLBenchmarks benchmarks =
            [ MkBenchmark
                { baseDir = "out/EPFL-benchmarks" </> category </> name
                , modA
                , modB
                }
            | (category, name) <- benchmarks
            , let modA = "orig"
            , modB <- ["orig_blif", "best_size", "best_depth"]
            ]

    phony "epfl" $ need ["out/EPFL-benchmarks/summary.csv"]
    "out/EPFL-benchmarks/summary.csv" %> \out -> do
        verilogFiles <- getDirectoryFiles "" ["EPFL-benchmarks/arithmetic/*.v", "EPFL-benchmarks/random_control/*.v"]
        benchmarksReport out $
            mkEPFLBenchmarks
                [ (category, name)
                | verilogFile <- verilogFiles
                , let Just [category, name] = filePattern "EPFL-benchmarks/*/*.v" verilogFile
                ]

    -- Quick EPFL benchmarks: those that complete in under ~20s in the cvc5 run
    phony "epfl-quick" $ need ["out/EPFL-benchmarks/quick_summary.csv"]
    "out/EPFL-benchmarks/quick_summary.csv" %> \out -> do
        benchmarksReport out $
            mkEPFLBenchmarks
                [ ("arithmetic", "adder")
                , ("arithmetic", "bar")
                , ("arithmetic", "max")
                , ("random_control", "arbiter")
                , ("random_control", "cavlc")
                , ("random_control", "ctrl")
                , ("random_control", "dec")
                , ("random_control", "i2c")
                , ("random_control", "int2float")
                , ("random_control", "priority")
                , ("random_control", "router")
                , ("random_control", "voter")
                ]

    -- PULP ELAU -------------------------------------------------------------

    phony "pulp-elau-to-smt" $ need ["out/pulp-elau/to_smt_summary.csv"]
    "out/pulp-elau/to_smt_summary.csv" %> \out -> do
        sourceFiles <- getDirectoryFiles "pulp-elau/src/" ["*.sv"]
        let logFiles =
                [ (design, variant, "out" </> "pulp-elau" </> design </> variant <.> target)
                | sourceFile <- sourceFiles
                , let design = dropExtension sourceFile
                , design /= "arith_utils"
                , variant <- ["slow", "medium", "fast"]
                , target <- ["lowered.vera"]
                ]
        need [f | (_, _, f) <- logFiles]

        liftIO $ T.writeFile out $ (T.pack "Benchmark,Speed,Result\n")
        forM_ logFiles $ \(design, variant, outFile) -> liftIO $ do
            outText <- readFile outFile
            logText <- readFile (outFile <.> "log")
            let result =
                    if or [msg `isInfixOf` txt | msg <- ["Error", "exception"], txt <- [outText, logText]]
                        then "Error"
                        else "OK"

            appendFile out $ intercalate "," [design, variant, result]
            appendFile out $ "\n"

    phony "pulp-elau" $ need ["out/pulp-elau/summary.csv"]
    "out/pulp-elau/summary.csv" %> \out -> do
        sourceFiles <- getDirectoryFiles "pulp-elau/src/" ["*.sv"]
        benchmarksReport out $
            [ MkBenchmark
                { baseDir = "out" </> "pulp-elau" </> design
                , modA
                , modB
                }
            | sourceFile <- sourceFiles
            , let design = dropExtension sourceFile
            , design /= "arith_utils"
            , (modA, modB) <- [("slow", "medium"), ("slow", "fast"), ("medium", "fast")]
            ]

    "out/pulp-elau/*/*.sv" !%> \out [design, variant] -> do
        let top :: String = case variant of
                "behavioural" -> "behavioural_" ++ design
                _ -> design
            speed = case variant of
                "behavioural" -> ""
                "slow" -> "-G speed=lau_pkg::SLOW"
                "medium" -> "-G speed=lau_pkg::MEDIUM"
                "fast" -> "-G speed=lau_pkg::FAST"
                _ -> error ("Invalid variant: " ++ variant)
            log = out <.> "log"
        cmd_
            (FileStdout log)
            (FileStderr log)
            "yosys"
            "--commands"
            [ printf
                "read_slang pulp-elau/src/*.sv --top %s %s; flatten; write_verilog %s"
                top
                speed
                out ::
                String
            ]

    "out/pulp-elau/*/*.lowered.vera.log" %> \out -> need [dropExtension out]
    "out/pulp-elau/*/*.lowered.vera" !%> \out [design, variant] -> do
        let src = "out/pulp-elau" </> design </> variant <.> "sv"
            log = out <.> "log"
        timeout <- askOracle ConfigVeraTimeout
        veraMemoryLimit <- askOracle ConfigVeraMemoryLimit
        need [vera, src]
        (Exit exitCode) <-
            cmd
                (Traced "vera")
                (Timeout timeout)
                (FileStdout out)
                (FileStderr log)
                (AddEnv "OCAMLRUNPARAM" "b")
                (AddEnv "VERA_MAX_MEMORY" (show (gibiBytes veraMemoryLimit)))
                (AddEnv "VERA_TRACE" "1")
                vera
                "lower"
                "smt"
                src
        return ()

--------------------------------------------------------------------------

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

-- `need`, then T.read a file
readFileT' :: FilePath -> Action Text
readFileT' fp = need [fp] >> liftIO (T.readFile fp)

-- T.writeFile, lifted to actions
writeFileT' :: FilePath -> Text -> Action ()
writeFileT' fp txt = liftIO (T.writeFile fp txt) >> trackWrite [fp]
