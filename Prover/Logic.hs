module Logic (tryAll, module Logic.Base, module Logic.DSL, module Logic.Rules, module Logic.Parsing) where


import           Control.Arrow (first)
import           Control.Parallel.Strategies
import           Data.Void (Void)
import           Data.Map (Map)
import qualified Data.Map as M

import           Prover
import           Logic.Base hiding (Term)
import           Logic.DSL
import           Logic.Rules
import           Logic.Printing ()
import           Logic.Parsing


tryAll :: (NFData r)
          => Map String (Term ConId Void)
          -> [Rule r ConId Int]
          -> String
          -> Term ConId Void
          -> [(Term ConId Void,[Term r Void])]
tryAll lexicon rules sentence y =
  case mapM (`M.lookup` lexicon) (words sentence) of
   Just formulas -> map ((\g -> (g, findAll g rules))
                        .(\x -> Con JFocusR [x,y]))
                    (brackets (·⊗·) formulas)
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
