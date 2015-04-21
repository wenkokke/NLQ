{-# LANGUAGE OverloadedStrings, ViewPatterns, FlexibleContexts, PartialTypeSignatures, TupleSections, RecordWildCards #-}
module Main where


import Prelude hiding (lex)
import Control.Monad (when,unless)
import Data.Char (isSpace)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.Void (Void)
import System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import System.Directory (doesFileExist)
import System.Environment (getProgName,getArgs)
import System.Exit (exitSuccess)
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
              , optTarget  = tgt
              , optGoal    = g
              , optDepth   = d
              } = opts

  when (null tasks)
       (putStrLn "Usage: For basic information, try the `--help' option.")

  let
    handle :: Task -> IO [(Maybe String, (Term ConId Void, Proof))]
    handle (Solve str) = case parse judgement "" str of
      Left  m -> error (show m)
      Right g -> return $ map ((Nothing,) . (g,)) (findAll g (getRules sys))
    handle (Parse sent) = case mbLexicon of
      Nothing  -> error "No lexicon file given."
      Just lex -> return $ map (Just sent,) (tryAll d lex sys sent g)

  proofs <- concat <$> mapM handle tasks

  let agdaFile modName = toAgdaFile modName sys (map setDefaultName proofs) g

  case tgt of
    StdOut             -> mapM_ printResult proofs
    AgdaFile  Nothing  -> putStr (agdaFile "Main")
    AgdaFile (Just fn) -> do checkFile fn; writeFile fn (agdaFile (takeBaseName fn))


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

printResult :: (Maybe String, (Term ConId Void, Proof)) -> IO ()
printResult (Nothing  , (g, p)) = do print (Agda g); print p
printResult (Just sent, (g, p)) = do putStrLn sent; print (Agda g); print p

setDefaultName :: (Maybe String, (Term ConId Void, Proof)) -> (String, (Term ConId Void, Proof))
setDefaultName (m,(g,p)) = (fromMaybe (defaultName g) m, (g,p))

defaultName :: Term ConId Void -> String
defaultName = map repl . filter (not . isSpace) . show . Agda
  where
    repl '(' = '['
    repl ')' = ']'
    repl  c  =  c


data Task
  = Solve String
  | Parse String

data Target
  = StdOut
  | AgdaFile (Maybe FilePath)

data Options = Options
  { optTasks      :: [Task]
  , optLexicon    :: Maybe (Map String (Term ConId Void))
  , optSystem     :: System
  , optTarget     :: Target
  , optGoal       :: Term ConId Void
  , optDepth      :: Int
  }

defaultOptions :: Options
defaultOptions    = Options
  { optTasks      = []
  , optLexicon    = Nothing
  , optSystem     = POLNL
  , optTarget     = StdOut
  , optGoal       = Con (Atom "s⁻") []
  , optDepth      = 5
  }

options :: [ OptDescr (Options -> IO Options) ]
options =
  [ Option [] ["solve"]
    (ReqArg (\arg opt -> return opt { optTasks = optTasks opt ++ [Solve arg] }) "SEQUENT")
    "Search for proof of a sequent."
  , Option [] ["parse"]
    (ReqArg (\arg opt -> return opt { optTasks = optTasks opt ++ [Parse arg] }) "SENTENCE")
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
