{-# LANGUAGE OverloadedStrings, FlexibleContexts, PartialTypeSignatures #-}
module Main where


import Data.Char (toLower)
import Data.Map (Map)
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
              , optLexicon = mbLexicon
              , optSystem  = system
              , optTarget  = tgt
              , optModule  = modName
              } = opts
  let rules = getRules system
  case task of
   Nothing -> putStrLn "Usage: For basic information, try the `--help' option."

   Just (Solve str) ->
     case parse judgement "" str of
      Left err -> print err
      Right tm -> mapM_ print (findAll tm rules)

   Just (Parse sent) ->
     case mbLexicon of
      Nothing      -> putStrLn "Error: No lexicon file given."
      Just lexicon -> putStr (toAgdaFile modName sent system (tryAll lexicon rules sent tgt) tgt)


parseTarget :: String -> IO (Term ConId Void)
parseTarget str = case parse formula "" str of
  Left err -> fail ("Error: Could not parse target formula `"++show str++"'\n"++show err)
  Right tm -> return tm


parseLexicon :: FilePath -> IO (Map String (Term ConId Void))
parseLexicon lexiconFile = do
  lexiconContent <- readFile lexiconFile
  case parse lexicon lexiconFile lexiconContent of
   Left  err     -> fail ("Error: Could not parse lexicon.\n"++show err)
   Right lexicon -> return lexicon


data Task
  = Solve String
  | Parse String

data Options = Options
  { optTask    :: Maybe Task
  , optLexicon :: Maybe (Map String (Term ConId Void))
  , optSystem  :: System
  , optTarget  :: Term ConId Void
  , optModule  :: String
  }

defaultOptions :: Options
defaultOptions = Options
  { optTask    = Nothing
  , optLexicon = Nothing
  , optSystem  = NL
  , optTarget  = Con (Atom "s⁻") []
  , optModule  = "Main"
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
    (ReqArg (\arg opt -> do lex <- parseLexicon arg
                            return opt { optLexicon = Just lex }) "LEXICON_FILE")
    "Lexicon (for parsing)"
  , Option "m" ["module"]
    (ReqArg (\arg opt -> return opt { optModule = arg }) "MODULE_NAME")
    "The module name for the generated Agda file"
  , Option "s" ["system"]
    (ReqArg (\arg opt -> return opt { optSystem = parseSystem arg }) "SYSTEM")
    "Logical system (NL, fNL, CNL, fCNL, LG, fLG)"
  , Option "t" ["target"]
    (ReqArg (\arg opt -> do tgt <- parseTarget arg
                            return opt { optTarget = tgt }) "TARGET")
    "Target formula (n,np,s⁻)"
  , Option "h" ["help"]
    (NoArg  (\_ -> do
              prg <- getProgName
              hPutStrLn stderr (usageInfo prg options)
              exitSuccess))
    "Show help"
  ]
