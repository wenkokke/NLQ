{-# LANGUAGE OverloadedStrings, ViewPatterns, FlexibleContexts, PartialTypeSignatures, TupleSections, RecordWildCards #-}
module Main where


import Prelude hiding (lex)
import Control.Monad (when,unless)
import Data.Map (Map)
import Data.Void (Void)
import System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import System.Directory (doesFileExist)
import System.Environment (getProgName,getArgs)
import System.Exit (exitSuccess, exitFailure)
import System.FilePath (takeBaseName)
import System.IO
import Text.Parsec (parse)


import Logic


main :: IO ()
main = do

  args <- getArgs

  let (actions, _, _) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTasks   = tasks
              , optLexicon = mbLexicon
              , optSystem  = sys
              , optOutput  = out
              , optGoal    = g
              , optDepth   = d
              } = opts

  when (null tasks)
       (putStrLn "Usage: For basic information, try the `--help' option.")

  let
    handle :: Task -> IO [Result]
    handle (Solve str) = case parse judgement "" str of
      Left  m -> error (show m)
      Right g -> return $ map (Solved (castVar g)) (findAll g (getRules sys))
    handle (Parse sent expr) = case mbLexicon of
      Just lex -> return (map (uncurry $ Parsed sent expr) (tryAll d lex sys sent g))
      _        -> error "No lexicon file given."

  proofs <- concat <$> mapM handle tasks

  let agdaFile modName = toAgdaFile modName sys proofs g

  case out of
    StdOut             -> mapM_ printResult proofs
    AgdaFile  Nothing  -> putStr (agdaFile "Main")
    AgdaFile (Just fn) -> do checkFile fn; writeFile fn (agdaFile (takeBaseName fn))


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


printResult :: Result -> IO ()
printResult (Solved     g p) = do print (Agda g); print p
printResult (Parsed s _ g p) = do putStrLn s; print (Agda g); print p


data Task
  = Solve String
  | Parse String [String]


data Output
  = StdOut
  | AgdaFile (Maybe FilePath)


data Options = Options
  { optTasks      :: [Task]
  , optLexicon    :: Maybe (Map String (Term ConId Void))
  , optSystem     :: System
  , optOutput     :: Output
  , optGoal       :: Term ConId Void
  , optDepth      :: Int
  }


defaultOptions :: Options
defaultOptions    = Options
  { optTasks      = []
  , optLexicon    = Nothing
  , optSystem     = POLNL
  , optOutput     = StdOut
  , optGoal       = Con (Atom "s⁻") []
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
    (ReqArg addResult "EXPRESSION")
    "Generate check if the previous test results in this expression."

  , Option "l" ["lexicon"]
    (ReqArg (\arg opt -> do lex <- parseLex arg; return opt { optLexicon = Just lex }) "LEXICON_FILE")
    "Lexicon used in parsing."

  , Option "s" ["system"]
    (ReqArg (\arg opt -> return opt { optSystem = parseSystem arg }) "SYSTEM")
    "Logical system (see below)."

  , Option "g" ["goal"]
    (ReqArg (\arg opt -> do g <- parseGoal arg; return opt { optGoal = g }) "GOAL_FORMULA")
    "Goal formula (n, np, s⁻, etc)."

  , Option [] ["to-agda"]
    (OptArg (\arg opt -> return opt { optOutput = AgdaFile arg }) "AGDA_FILE")
    "Produce an Agda module, and write it to the given file (or stdout)."

  , Option "d" ["depth"]
    (ReqArg (\arg opt -> return opt { optDepth = read arg }) "SEARCH_DEPTH")
    "Search depth (for systems with infinite search spaces)"

  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              hPutStrLn stderr descAll
              exitSuccess))
    "Show help."
  ]


-- |Check if given Task is a parse-task with no expected result.
isParse :: Task -> Bool
isParse (Parse _ _) = True
isParse _           = False


addResult :: String -> Options -> IO Options
addResult expr opt@Options{..} = do
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


parseGoal :: String -> IO (Term ConId Void)
parseGoal str = case parse formula "" str of
  Left err -> fail ("Could not parse goal formula `"++show str++"'.\n"++show err)
  Right tm -> return tm

parseLex :: FilePath -> IO (Map String (Term ConId Void))
parseLex lexiconFile = do
  lexiconContent <- readFile lexiconFile
  case parse lexicon lexiconFile lexiconContent of
   Left  err -> fail ("Could not parse lexicon.\n"++show err)
   Right lex -> return lex
