{-# LANGUAGE OverloadedStrings, ViewPatterns, FlexibleContexts, PartialTypeSignatures #-}
module Main where


import Prelude hiding (lex)
import Data.Map (Map)
import Data.Void (Void)
import System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import System.Environment (getProgName,getArgs)
import System.Exit (exitSuccess)
import System.FilePath (takeBaseName)
import System.IO (hPutStrLn,stderr)
import Text.Parsec (parse)


import Logic


main :: IO ()
main = do

  args <- getArgs

  let (actions, _, _) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTask    = task
              , optLexicon = mbLexicon
              , optSystem  = sys
              , optTarget  = tgt
              , optGoal    = g
              , optDepth   = d
              } = opts
  case task of
   Nothing -> putStrLn "Usage: For basic information, try the `--help' option."

   Just (Solve str) ->
     case parse judgement "" str of
      Left err -> print err
      Right tm -> mapM_ print (findAll tm (getRules sys))

   Just (Parse sent) ->
     case mbLexicon of
      Nothing  -> putStrLn "Error: No lexicon file given."
      Just lex -> let

        prfs = tryAll d lex sys sent g

        in case tgt of
            StdOut             -> mapM_ (\(j,p) -> do print (Agda j); print p) prfs
            AgdaFile  Nothing  -> putStr $ toAgdaFile "Main" sent sys prfs g
            AgdaFile (Just fn) -> return ()

data Task
  = Solve String
  | Parse String

data Target
  = StdOut
  | AgdaFile (Maybe FilePath)

data Options = Options
  { optTask       :: Maybe Task
  , optLexicon    :: Maybe (Map String (Term ConId Void))
  , optSystem     :: System
  , optTarget     :: Target
  , optGoal       :: Term ConId Void
  , optDepth      :: Int
  }

defaultOptions :: Options
defaultOptions    = Options
  { optTask       = Nothing
  , optLexicon    = Nothing
  , optSystem     = NL
  , optTarget     = StdOut
  , optGoal       = Con (Atom "s⁻") []
  , optDepth      = 5
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> return opt { optTask = Just (Solve arg) }) "SEQUENT")
    "Search for proof of a sequent."
  , Option [] ["parse"]
    (ReqArg (\arg opt -> return opt { optTask = Just (Parse arg) }) "SENTENCE")
    "Parse the given sentence."
  , Option "l" ["lexicon"]
    (ReqArg (\arg opt -> do lex <- parseLex arg; return opt { optLexicon = Just lex }) "LEXICON_FILE")
    "Lexicon used in parsing."
  , Option "s" ["system"]
    (ReqArg (\arg opt -> return opt { optSystem = parseSystem arg }) "SYSTEM")
    "Logical system (NL, fNL, CNL, fCNL, LG, fLG, EXP)."
  , Option "g" ["goal"]
    (ReqArg (\arg opt -> do g <- parseGoal arg; return opt { optGoal = g }) "GOAL_FORMULA")
    "Goal formula (n, np, s⁻)."
  , Option [] ["to-agda"]
    (OptArg (\arg opt -> return opt { optTarget = AgdaFile arg }) "AGDA_FILE")
    "Target Agda file."
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
