{-# LANGUAGE OverloadedStrings #-}
module Main where


import           Data.Void (Void)
import           System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import           System.Environment (getProgName,getArgs)
import           System.Exit (exitSuccess)
import           System.IO (hPutStrLn,stderr)
import           Text.Parsec (parse)
import           Prover hiding (Term)
import           LambekGrishin.Base
import           LambekGrishin.Rules
import           LambekGrishin.Printing ()
import           LambekGrishin.Parsing (judgement,lexicon)


main :: IO ()
main = do

  args <- getArgs

  let (actions, nonOptions, errors) = getOpt Permute options args
  opts <- foldl (>>=) (return defaultOptions) actions
  let Options { optTask    = task
              , optLexicon = mbLexicon
              } = opts
  case task of
   Nothing          -> return ()
   Just (Solve str) -> do
     case parse judgement "" str of
      Left err -> print err
      Right tm -> print (search tm rules)
   Just (Parse str) -> return ()



data Task = Solve String
          | Parse String

data Options = Options
  { optTask    :: Maybe Task
  , optLexicon :: Maybe FilePath
  }

defaultOptions :: Options
defaultOptions = Options
  { optTask    = Nothing
  , optLexicon = Nothing
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> do return opt { optTask = Just (Solve arg) }) "SEQUENT")
    "Search for proof of a sequent"
  , Option [] ["parse"]
    (ReqArg (\arg opt -> do return opt { optTask = Just (Parse arg) }) "SENTENCE")
    "Parse the given sentence"
  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              exitSuccess))
    "Show help"
  ]
