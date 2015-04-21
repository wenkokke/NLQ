{-# LANGUAGE RecordWildCards, TupleSections #-}
module Logic (tryAll, module X) where


import           Control.Arrow (first)
import           Control.Parallel.Strategies

import           Prelude hiding (lex)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (maybe)
import           Data.List (nub)
import           Data.Void (Void)


import           Logic.Prover   as X
import           Logic.Base     as X hiding (Term)
import           Logic.Rules    as X
import           Logic.Printing as X (Agda(..),ASCII(..))
import           Logic.Parsing  as X
import           Logic.System   as X
import           Logic.ToAgda   as X


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
tryAll d lex sys sent g =
  (if isFinite then finiteProofs else infiniteProofs) `using` parList rdeepseq
  where
    SysInfo{..} = getSysInfo sys

    baseFormulas   = lookupAll lex (words sent)
    baseStructures = maybe baseFormulas (\f -> map (unary f) baseFormulas) downOp
    leftHandSides  = brackets (unary <$> unaryOp) (binary binaryOp) baseStructures
    judgements     = map (\x -> binary sequent x g) leftHandSides
    finiteProofs   = concatMap (\j -> map (j,) (findAll j rules)) judgements
    infiniteProofs = findFirst d judgements rules


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
