{-# LANGUAGE OverloadedStrings, ViewPatterns, FlexibleContexts, PartialTypeSignatures, TupleSections, RecordWildCards #-}
module Main where


import           Prelude hiding (lex)
import           Control.Arrow (first)
import           Control.Monad (when,unless)
import           Control.Parallel.Strategies
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (maybe,listToMaybe)
import           Data.List (nub)
import           Data.Void (Void)
import           System.Console.GetOpt (OptDescr(..),ArgDescr(..),ArgOrder(..),usageInfo,getOpt)
import           System.Directory (doesFileExist)
import           System.Environment (getProgName,getArgs)
import           System.Exit (exitSuccess, exitFailure)
import           System.FilePath (takeBaseName)
import           System.IO
import           Text.Parsec (parse)

import           CG.Prover
import           CG.Base hiding (Term)
import           CG.Rules
import           CG.Printing (Agda(..),ASCII(..))
import           CG.Parsing
import           CG.System
import           CG.ToAgda


-- * Options

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


-- * Main function

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


-- * Parsing utilities

-- |Create all possible structures from a list of formulas, joining
--  them with the binary structural connective @·⊗·@, and then find
--  all proofs for each of these structures, returning a list of
--  structures paired with their proofs.
--  Note: the resulting list may contain pairs for structures for
--  which no proofs were found.
tryAll :: Int                          -- ^ Search depth
       -> Map String (Term ConId Void) -- ^ Lexicon
       -> System                       -- ^ Inference system
       -> String                       -- ^ Sentence
       -> Term ConId Void              -- ^ Goal formula
       -> [(Term ConId Void,Term RuleId Void)]
tryAll d lex sys sent g = resultList `using` parList rdeepseq
  where
    SysInfo{..}    = getSysInfo sys
    downOp         = if structural then Just Down else Nothing

    baseFormulas   = lookupAll lex (words sent)
    baseStructures = maybe baseFormulas (\f -> map (unary f) baseFormulas) downOp
    leftHandSides  = brackets (unary <$> listToMaybe unaryOp) (binary (head binaryOp)) baseStructures
    judgements     = map (\x -> binary sequent x g) leftHandSides
    finiteProofs   = concatMap (\j -> map (castVar j,) (findAll j rules)) judgements
    infiniteProofs = map (first castVar) (findFirst d judgements rules)
    resultList     = if finite then finiteProofs else infiniteProofs


-- |Look up all words in a given list of words in a lexicon.
lookupAll :: Map String (Term ConId Void) -- ^ Lexicon
          -> [String]                     -- ^ Sentence
          -> [Term ConId Void]
lookupAll _   [    ] = []
lookupAll lex (w:ws) = case M.lookup w lex of
  Just tm -> tm : lookupAll lex ws
  Nothing -> error ("Cannot find `"++w++"' in the lexicon.")


-- |Generate all binary trees with n nodes, formed by applications of
--  a given binary operator, with at most one application of a given
--  unary operator at every node.
brackets :: (Eq a) => Maybe (a -> a) -> (a -> a -> a) -> [a] -> [a]
brackets mbPre op = nub . brack where

  brack [ ] = [ ]
  brack [x] = [x]
  brack lst = maybe (rec id) (\pre -> rec id ++ rec pre) mbPre
    where
      rec f = [ f (l `op` r) | (ls,rs) <- split lst, l <- brack ls, r <- brack rs ]

  split [_]    = []
  split (x:xs) = ([x],xs) : map (first (x:)) (split xs)


-- * IO utilities

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


-- * Option utilities

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
