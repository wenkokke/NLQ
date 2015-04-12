{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Main where


import Data.Char (toLower)
import Data.Void (Void)
import System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import System.Environment (getProgName,getArgs)
import System.Exit (exitSuccess)
import System.IO (hPutStrLn,stderr)
import Text.Parsec (parse)

import Logic
import Prover

main :: IO ()
main = do

  args <- getArgs

  let (actions, nonOptions, errors) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTask    = task
              , optLexicon = mbLexiconFile
              , optSystem  = system
              , optTarget  = mbTarget
              } = opts
  let rules = getRules system
  case task of
   Nothing -> putStrLn "Usage: For basic information, try the `--help' option."

   Just (Solve str) ->
     case parse judgement "" str of
      Left err -> print err
      Right tm -> mapM_ print (findAll tm rules)

   Just (Parse str) ->
     case mbTarget of
      Nothing     -> putStrLn "no target formula given"
      Just targetStr ->
        case parse formula "" targetStr of
         Left err     -> print err
         Right target ->
           case mbLexiconFile of
            Nothing          -> putStrLn "no lexicon given"
            Just lexiconFile -> do
              lexiconContent <- readFile lexiconFile
              case parse lexicon lexiconFile lexiconContent of
               Left  err     -> print err
               Right lexicon -> mapM_ printResult (tryAll lexicon rules str target)
                 where
                   printResult (g,[]) = return ()
                   printResult (g,ps) = do print g; mapM_ print ps


getRules :: String -> [Rule String ConId Int]
getRules (map toLower ->  "nl") = lambek
getRules (map toLower -> "fnl") = polarisedLambek
getRules (map toLower ->  "lg") = lambekGrishin
getRules (map toLower -> "flg") = polarisedLambekGrishin
getRules str = error ("unknown system '"++str++"'")


data Task
  = Solve String
  | Parse String

data System
  = Lambek
  | LambekGrishin
  | PolarisedLambekGrishin

data Options = Options
  { optTask    :: Maybe Task
  , optLexicon :: Maybe FilePath
  , optSystem  :: String
  , optTarget  :: Maybe String
  }

defaultOptions :: Options
defaultOptions = Options
  { optTask    = Nothing
  , optLexicon = Nothing
  , optSystem  = "nl"
  , optTarget  = Just "s⁻"
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> return opt { optTask = Just (Solve arg) }) "SEQUENT")
    "Search for proof of a sequent"
  , Option [] ["parse"]
    (ReqArg (\arg opt -> return opt { optTask = Just (Parse arg) }) "SENTENCE")
    "Parse the given sentence"
  , Option "l" ["lexicon"]
    (ReqArg (\arg opt -> return opt { optLexicon = Just arg }) "LEXICON_FILE")
    "Lexicon (for parsing)"
  , Option "s" ["system"]
    (ReqArg (\arg opt -> return opt { optSystem = arg }) "SYSTEM")
    "Logical system (NL, fNL, LG, fLG)"
  , Option "t" ["target"]
    (ReqArg (\arg opt -> return opt { optTarget = Just arg }) "TARGET")
    "Target formula (n,np,s⁻)"
  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              exitSuccess))
    "Show help"
  ]
