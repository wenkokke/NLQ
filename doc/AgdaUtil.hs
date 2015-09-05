module AgdaUtil (agda_path,compute_toplevel) where

import Data.List (isPrefixOf)
import System.Environment (getEnv)
import System.FilePath (splitSearchPath)
import System.IO
import System.Process
import Text.Printf (printf)


-- | Extract normal forms from an Agda interaction response.
nfs :: [String] -> [String]
nfs = map nf . filter (nf_prefix `isPrefixOf`)
  where
    nf = read . read . reverse . drop (length nf_suffix) . reverse . drop (length nf_prefix)
    nf_prefix = "(agda2-info-action \"*Normal Form*\" "
    nf_suffix = " nil)"

-- | Look up the Agda search path.
agda_path :: IO [FilePath]
agda_path = splitSearchPath <$> getEnv "AGDA_PATH"


-- | Compute the command string for loading an Agda file.
cmd_load :: FilePath -> [String] -> String
cmd_load file path
  = printf "IOTCM %s NonInteractive Indirect ( Cmd_load %s %s )"
    (show file) (show file) (show path)


-- | Compute the command string for computing a normal form.
cmd_compute_toplevel :: FilePath -> String -> String
cmd_compute_toplevel file expr
  =  printf "IOTCM %s None Indirect ( Cmd_compute_toplevel False %s )"
     (show file) (show expr)


-- | Load a file into Agda interaction and request a series of normal forms.
compute_toplevel :: FilePath -> [String] -> IO [String]
compute_toplevel file exprs = do
  (hin,hout,herr,_) <- runInteractiveCommand "agda --interaction"

  hSetBinaryMode hin  False
  hSetBinaryMode hout False
  hSetBinaryMode herr False
  hSetBuffering  hin  LineBuffering
  hSetBuffering  hout NoBuffering
  hSetBuffering  herr NoBuffering

  agda_path' <- agda_path

  hPutStrLn hin (cmd_load file agda_path')
  sequence_ (hPutStrLn hin . cmd_compute_toplevel file <$> exprs)
  resp <- hGetContents hout

  return (nfs (lines resp))
