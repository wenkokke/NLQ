{-# LANGUAGE OverloadedStrings, ViewPatterns, FlexibleContexts, PartialTypeSignatures, TupleSections, RecordWildCards #-}
module Main where


import           Prelude hiding (lex)
import           Control.Monad (when,unless)
import           Data.List.Split (splitOn)
import           Data.Map (Map)
import           Data.Maybe (fromMaybe,maybe)
import           Data.Void (Void)
import           System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import           System.Directory (doesFileExist,createDirectoryIfMissing)
import           System.Environment (getProgName,getArgs,getEnv)
import           System.Exit (ExitCode(..), exitSuccess, exitFailure)
import           System.FilePath (takeBaseName,dropExtension,(</>),(<.>))
import           System.IO
import           System.Process
import qualified Text.Parsec as P (parse)

import           CG.Prover
import           CG.Parser
import           CG.Base hiding (Term)
import           CG.Parsing
import           CG.ToAgda



main :: IO ()
main = do

  args <- getArgs

  let (actions, _, _) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTasks   = tasks
              , optLexicon = mbLexicon
              , optSystem  = sys@System{..}
              , optOutput  = out
              , optGoal    = g
              , optDepth   = d
              } = opts

  when (null tasks)
       (putStrLn "Usage: For basic information, try the `--help' option.")

  let
    runTask :: Task -> IO [Result]
    runTask (Solve str) = case P.parse judgement "" str of
      Left  e -> error (show e)
      Right g -> return $ map (uncurry Solved) (solve sys d [g])
    runTask (Parse sent expr) = case mbLexicon of
      Just lx -> return (map (uncurry $ Parsed sent expr) (parse sys d lx sent g))
      _       -> error "No lexicon file given."

  proofs <- concat <$> mapM runTask tasks

  let
    generateAgda :: Maybe FilePath -> IO [FilePath]
    generateAgda  Nothing  = writeAgdaFile stdout "Main" sys proofs g
    generateAgda (Just fn) = withFile fn WriteMode (\h -> writeAgdaFile h (takeBaseName fn) sys proofs g)

    generateLaTeX :: Maybe FilePath -> IO [FilePath]
    generateLaTeX mbDir = do
      let targetDir = fromMaybe "." mbDir
      cgtoolHome <- getEnv "CGTOOL_HOME"
      let mainFile = cgtoolHome </> "Main.agda"
      createDirectoryIfMissing True cgtoolHome
      fileList <- withFile mainFile WriteMode
                  (\h -> writeAgdaFile h "Main" sys proofs g)
      compileAgda cgtoolHome mainFile
      readProcessWithExitCode (dropExtension mainFile) [] ""
      return fileList


  case out of
    StdOut         -> mapM_ printResult proofs
    AgdaFile fn -> do maybe (return ()) checkFile fn; generateAgda fn; return ()
    LaTeX    mb -> do generateLaTeX mb >>= mapM_ (putStrLn . (++".tex"))



-- * Command-Line Options

data Task
  = Solve String
  | Parse String [String]

data Output
  = StdOut                    -- ^ Print proofs to the standard output.
  | AgdaFile (Maybe FilePath) -- ^ Convert proofs to an Agda program and print it.
  | LaTeX    (Maybe FilePath) -- ^ Convert proofs to LaTeX files.

data Options = Options
  { optTasks      :: [Task]
  , optLexicon    :: Maybe (Map String (Term ConId Void))
  , optSystem     :: System ConId
  , optOutput     :: Output
  , optGoal       :: Term ConId Void
  , optDepth      :: Int
  }

defaultOptions :: Options
defaultOptions    = Options
  { optTasks      = []
  , optLexicon    = Nothing
  , optSystem     = error "System must be specified."
  , optOutput     = StdOut
  , optGoal       = Con (NegAtom "s") []
  , optDepth      = 5
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> return opt { optTasks = optTasks opt ++ [Solve arg] }) "SEQUENT")
    "Search for proof of a sequent."

  , Option [] ["parse"]
    (ReqArg (\arg opt -> return opt { optTasks = optTasks opt ++ [Parse arg []] }) "SENTENCE")
    "Parse the given sentence."

  , Option [] ["to","or"]
    (ReqArg addExpected "EXPRESSION")
    "Generate check if the previous test results in this expression."

  , Option "l" ["lexicon"]
    (ReqArg (\arg opt -> do lex <- readLexicon arg; return opt { optLexicon = Just lex }) "LEXICON_FILE")
    "Lexicon used in parsing."

  , Option "s" ["system"]
    (ReqArg (\arg opt -> do sys <- readSystem arg; return opt { optSystem = sys }) "SYSTEM")
    "Logical system (see below)."

  , Option "g" ["goal"]
    (ReqArg (\arg opt -> do g <- parseGoal arg; return opt { optGoal = g }) "GOAL_FORMULA")
    "Goal formula (n, np, s⁻, etc)."

  , Option [] ["to-agda"]
    (OptArg (\arg opt -> do return opt { optOutput = AgdaFile arg }) "AGDA_FILE")
    "Produce an Agda module, and write it to the given file (or stdout)."

  , Option [] ["to-latex"]
    (OptArg (\arg opt -> do return opt { optOutput = LaTeX arg }) "DIRECTORY")
    "Produce a TeX and a PNG file for each proof."

  , Option "d" ["depth"]
    (ReqArg (\arg opt -> return opt { optDepth = read arg }) "SEARCH_DEPTH")
    "Search depth (for systems with infinite search spaces)"

  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              exitSuccess))
    "Show help."
  ]



-- * Helper functions

compileAgda :: FilePath -> FilePath -> IO ExitCode
compileAgda dir mainFile = do
  agdaInclude <- map ("-i"++) . (dir:) . splitOn ":" <$> getEnv "AGDA_PATH"
  let args = "--compile" : "--compile-dir" : dir : agdaInclude ++ [mainFile]
  --putStrLn (showCommandForUser "agda" args)
  (ext,out,err) <- readProcessWithExitCode "agda" args ""
  case ext of
   ExitSuccess -> return ExitSuccess
   _           -> do hPutStrLn stdout out; hPutStrLn stderr err; return ext


hOpen :: Maybe FilePath -> IO Handle
hOpen  Nothing  = return stdout
hOpen (Just fn) = openFile fn WriteMode

-- |Check if a given file exists, and if so ask for a confirmation
--  for overwriting the file.
checkFile :: FilePath -> IO ()
checkFile fn = do
  fileExists <- doesFileExist fn
  unless fileExists $ do
    hSetBuffering stdout NoBuffering
    putStr (fn ++ " exists. Overwrite? (y/n) ")
    hSetBuffering stdin NoBuffering
    hSetEcho stdin False
    hFlushInput stdin
    answer <- yorn
    when (answer == 'Y') exitSuccess
  where
    hFlushInput hdl = do
      r <- hReady hdl
      when r (hGetChar hdl >> hFlushInput hdl)

    yorn = do
      c <- getChar
      if c == 'Y' || c == 'N' then return c
      else if c == 'y' then return 'Y'
      else if c == 'n' then return 'N'
      else yorn


-- |Print results.
printResult :: Result -> IO ()
printResult (Solved     g p) = do print g; print p
printResult (Parsed s _ g p) = do putStrLn s; print g; print p


-- |Add an expected result to the most recent @Parse@ task.
addExpected :: String -> Options -> IO Options
addExpected expr opt@Options{..} = do
  progName <- getProgName

  when (null optTasks) $
    do putStrLn ("Usage: "++progName++"--parse SENTENCE --to "
                 ++"EXPRESSION [--or EXPRESSION]"); exitFailure

  let lastTask = last optTasks

  unless (isParse lastTask) $
    do putStrLn ("Usage: "++progName++"--parse SENTENCE --to "
                 ++"EXPRESSION [--or EXPRESSION]"); exitFailure

  let (Parse sent exprs) = lastTask
  return opt { optTasks = init optTasks ++ [Parse sent (exprs ++ [expr])]}


-- |Check if given Task is a parse-task with no expected result.
isParse :: Task -> Bool
isParse (Parse _ _) = True
isParse _           = False
