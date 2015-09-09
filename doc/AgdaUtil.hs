module AgdaUtil (agdaPath,resolvePath,computeTopLevel) where

import Data.List (isPrefixOf)
import Control.Monad (filterM)
import System.Directory (doesFileExist)
import System.Environment (getEnv)
import System.FilePath ((</>),isRelative,splitSearchPath)
import System.IO (BufferMode(..),hSetBinaryMode,hSetBuffering,hPutStrLn,hGetContents)
import System.Process (runInteractiveCommand)
import Text.Printf (printf)


-- | Extract normal forms from an Agda interaction response.
nfs :: [String] -> [String]
nfs = map nf . filter (nf_prefix `isPrefixOf`)
  where
    nf = read . read . reverse . drop (length nf_suffix) . reverse . drop (length nf_prefix)
    nf_prefix = "(agda2-info-action \"*Normal Form*\" "
    nf_suffix = " nil)"


-- | Look up the Agda search path.
agdaPath :: IO [FilePath]
agdaPath = splitSearchPath <$> getEnv "AGDA_PATH"


-- | Compute the command string for loading an Agda file.
cmdLoad :: FilePath -> [String] -> String
cmdLoad file path
  = printf "IOTCM %s NonInteractive Indirect ( Cmd_load %s %s )"
    (show file) (show file) (show path)


-- | Compute the command string for computing a normal form.
cmdComputeTopLevel :: FilePath -> String -> String
cmdComputeTopLevel file expr
  =  printf "IOTCM %s None Indirect ( Cmd_compute_toplevel False %s )"
     (show file) (show expr)


-- | Load a file into Agda interaction and request a series of normal forms.
computeTopLevel :: FilePath -> [String] -> IO [String]
computeTopLevel file exprs = do
  (hin,hout,herr,_) <- runInteractiveCommand "agda --interaction"

  hSetBinaryMode hin  False
  hSetBinaryMode hout False
  hSetBinaryMode herr False
  hSetBuffering  hin  LineBuffering
  hSetBuffering  hout NoBuffering
  hSetBuffering  herr NoBuffering

  agdaPath' <- agdaPath

  hPutStrLn hin (cmdLoad file agdaPath')
  sequence_ (hPutStrLn hin . cmdComputeTopLevel file <$> exprs)
  resp <- hGetContents hout

  let result = nfs (lines resp)

  if null result
    then error resp
    else return result


-- | Disambiguate a filepath.
resolvePath :: FilePath -> IO FilePath
resolvePath file =
  if isRelative file
    then do
    candidateDirs  <- agdaPath
    candidateFiles <- filterM doesFileExist (map (</> file) candidateDirs)
    if length candidateFiles == 1
      then return (head candidateFiles)
      else error ("resolvePath: ambiguous filepath "++show file
                  ++", could refer to any of "++show candidateFiles)
    else
    return file


{-
main :: IO ()
main = do
  args <- getArgs
  if length args < 2
    then error "Usage: AgdaUtil FILE EXPR [EXPR...]"
    else do
    path  <- resolvePath (head args)
    exprs <- computeTopLevel path (tail args)
    forM_ exprs putStrLn
-}
