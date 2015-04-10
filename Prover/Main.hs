{-# LANGUAGE OverloadedStrings, ViewPatterns #-}
module Main where


import Data.Char (toUpper)
import Data.Void (Void)
import System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import System.Environment (getProgName,getArgs)
import System.Exit (exitSuccess)
import System.IO (hPutStrLn,stderr)
import Text.Parsec (parse)
import LambekGrishin


main :: IO ()
main = do

  args <- getArgs

  let (actions, nonOptions, errors) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTask    = task
              , optLexicon = lexiconFile
              , optSystem  = system
              } = opts
  case task of

   Just (Solve str) ->
     case parse judgement "" str of
      Left err -> print err
      Right tm -> mapM_ print (search tm (rules system))

   Just (Parse str) ->
     case lexiconFile of
      Nothing          -> putStrLn ("no lexicon given")
      Just lexiconFile -> do
        lexiconContent <- readFile lexiconFile
        case parse lexicon lexiconFile lexiconContent of
         Left  err     -> print err
         Right lexicon -> return ()


rules :: System -> [Rule String ConId Int]
rules Lambek                 = lambek
rules LambekGrishin          = lambekGrishin
rules PolarisedLambekGrishin = polarisedLambekGrishin


parseSystem :: String -> System
parseSystem (map toUpper ->  "NL") = Lambek
parseSystem (map toUpper ->  "LG") = LambekGrishin
parseSystem (map toUpper -> "FLG") = PolarisedLambekGrishin


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
  , optSystem  :: System
  }

defaultOptions :: Options
defaultOptions = Options
  { optTask    = Nothing
  , optLexicon = Nothing
  , optSystem  = Lambek
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> do return opt { optTask = Just (Solve arg) }) "SEQUENT")
    "Search for proof of a sequent"
  , Option [] ["parse"]
    (ReqArg (\arg opt -> do return opt { optTask = Just (Parse arg) }) "SENTENCE")
    "Parse the given sentence"
  , Option "l" ["lexicon"]
    (ReqArg (\arg opt -> do return opt { optLexicon = Just arg }) "LEXICON_FILE")
    "Lexicon (for parsing)"
  , Option "s" ["system"]
    (ReqArg (\arg opt -> do return opt { optSystem = parseSystem arg }) "SYSTEM")
    "Logical system (NL, LG, fLG)"
  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              exitSuccess))
    "Show help"
  ]
