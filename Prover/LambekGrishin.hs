module LambekGrishin
       (tryAll
       ,module Prover
       ,module LambekGrishin.Base
       ,module LambekGrishin.DSL
       ,module LambekGrishin.Rules
       ,module LambekGrishin.Parsing
       ) where


import           Control.Arrow (first)
import           Control.Parallel.Strategies
import           Data.Void (Void)
import           Data.Map (Map)
import qualified Data.Map as M
import           Prover
import           LambekGrishin.Base hiding (Term)
import           LambekGrishin.DSL
import           LambekGrishin.Rules
import           LambekGrishin.Printing ()
import           LambekGrishin.Parsing


tryAll :: (NFData r)
          => Map String (Term ConId Void)
          -> [Rule r ConId Int]
          -> String
          -> Term ConId Void
          -> [(Term ConId Void,[Term r Void])]
tryAll lexicon rules sentence y =
  case mapM (`M.lookup` lexicon) (words sentence) of
   Just formulas -> map (\g -> (g, findAll g rules))
                    (map (\x -> Con JFocusR [x,y]) (brackets (·⊗·) formulas))
                    `using` parList rdeepseq
   _             -> []



-- | Generates all binary trees with n nodes. The naive algorithm.
brackets :: (a -> a -> a) -> [a] -> [a]
brackets op = brack where

  brack [ ] = [ ]
  brack [x] = [x]
  brack lst = [l `op` r | (ls,rs) <- split lst, l <- brack ls, r <- brack rs]

  split [_]    = []
  split (x:xs) = ([x],xs) : map (first (x:)) (split xs)
