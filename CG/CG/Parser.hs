{-# LANGUAGE TupleSections, RecordWildCards #-}
module CG.Parser (parse) where


import           Prelude hiding (lex)
import           CG.Base
import           Control.Arrow (first)
import           Control.Parallel.Strategies
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Void (Void)



-- * Parsing

-- |Create all possible structures from a list of formulas, joining
--  them with the binary structural connective @·⊗·@, and then find
--  all proofs for each of these structures, returning a list of
--  structures paired with their proofs.
--  Note: the resulting list may contain pairs for structures for
--  which no proofs were found.
parse :: System ConId                 -- ^ Inference system
       -> Int                          -- ^ Search depth
       -> Map String (Term ConId Void) -- ^ Lexicon
       -> String                       -- ^ Sentence
       -> Term ConId Void              -- ^ Goal formula
       -> [(Term ConId Void,Term RuleId Void)]
parse sys@System{..} d lex sent g =
  solve sys d judgements `using` parList rdeepseq
  where
    -- read the entries from the lexicon, wrapping them in a
    -- down constructor if the logic is structural
    entries = lookupAll lex (words sent)
    entries'
      | structural = map (unary Down) entries
      | otherwise  = entries

    -- construct the left-hand sides using the @brackets@ function
    leftHandSides = brackets (unary <$> unaryOp) (binary (unsafeBinaryOp sys)) entries'

    -- construct all possible judgements by combining them with
    -- the sequent and the goal formula
    sequent    = if structural then JFocusR else JAlgebr
    judgements = map (flip (binary sequent) g) leftHandSides



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
  brack lst = maybe (go id) (\pre -> go id ++ go pre) mbPre
    where
      go f = [ f (l `op` r) | (ls,rs) <- split lst, l <- brack ls, r <- brack rs ]

  split [_]    = []
  split (x:xs) = ([x],xs) : map (first (x:)) (split xs)


-- |Retrieve the single binary connective from the system, or throw an error.
unsafeBinaryOp :: System c -> c
unsafeBinaryOp System{..} = case binaryOp of
  [   ] -> error "Must set at least one binary operator to parse."
  [ f ] -> f
  (_:_) -> error "Parsing with multiple binary operators is not implemented."
