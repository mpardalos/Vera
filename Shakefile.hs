{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util
import Data.Tuple (swap)
import Data.List (isSuffixOf, isInfixOf, isPrefixOf, stripPrefix, unsnoc)
import Data.Bifunctor (bimap)
import Data.Char (isDigit)
import Data.Maybe (isJust)
import Control.Monad (forM_, guard)
import System.Directory qualified
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import Debug.Trace

vera :: FilePath
vera = "_build/install/default/bin/vera"

main :: IO ()
main = shakeArgs shakeOptions {shakeThreads=0} $ do
  phony "vera" $ need [vera]
  vera %> \out -> cmd_ "dune" "build"

  phony "clean" $ do
    need ["clean-synth", "clean-gen", "clean-run"]

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
      runAfter $ System.Directory.removeDirectoryRecursive ("examples" </> dir)

  -- Running vera
  "*.vera.time" %> \out -> need [ out -<.> "log" ]
  "*.vera.smt2" %> \out -> need [ out -<.> "log" ]
  "//*_vs_*.vera.log" %> \out -> do
    let Just [dir, mod1, mod2] = filePattern "//*_vs_*.vera.log" out
        smtFile = out -<.> "smt2"
        timeFile = out -<.> "time"
        left = dir </> mod1 <.> "sv"
        right = dir </> mod2 <.> "sv"
    need [vera, left, right]
    begin <- liftIO getCurrentTime
    cmd_
      (Traced "vera")
      (Timeout 60)
      (FileStdout out)
      (FileStderr out)
      "time" vera "compare" "--solver=cvc5" ("--dump-query=" ++ smtFile) left right
    end <- liftIO getCurrentTime
    writeFile' timeFile (show (diffUTCTime end begin))

  phony "clean-run" $ do
    removeFilesAfterVerbose "examples"
      ["//*.vera.log", "//*.vera.time", "//*.vera.smt2"]

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
