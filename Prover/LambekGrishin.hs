module LambekGrishin
       (module Prover
       ,module LambekGrishin.Base
       ,module LambekGrishin.Rules
       ,module LambekGrishin.Parsing
       ) where


import           Control.Arrow (first)
import           Data.Void (Void)
import           Data.Map (Map)
import qualified Data.Map as M
import           Prover hiding (Term)
import           LambekGrishin.Base
import           LambekGrishin.DSL ((·⊗·))
import           LambekGrishin.Rules
import           LambekGrishin.Printing ()
import           LambekGrishin.Parsing


--parser :: Map String (Term Void) -> String -> _
--parser lexicon sentence =
--  case mapM (`M.lookup` lexicon) (words sentence) of
--   Just formulas -> brackets (·⊗·) formulas
--   _             -> _


-- | Generates all binary trees with n nodes. The naive algorithm.
brackets :: (a -> a -> a) -> [a] -> [a]
brackets op = brack where

  brack [ ] = [ ]
  brack [x] = [x]
  brack lst = [l `op` r | (ls,rs) <- split lst, l <- brack ls, r <- brack rs]

  split [_]    = []
  split (x:xs) = ([x],xs) : map (first (x:)) (split xs)
