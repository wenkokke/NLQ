{-# LANGUAGE GADTs, RecordWildCards, FlexibleContexts #-}
module Prover.Prover where


import Prover.Base
import Prover.Match hiding ((++))

import qualified Data.Set as S
import Text.Printf (printf)


-- * Proof structures

data Proof where
  Con :: RuleName -> [Proof] -> Proof

type Proof' f = (Int, [f Int] , [Proof] -> Proof)

mkProof :: Rule f Int -> [Proof] -> [Proof]
mkProof Rule{..} xs = first : rest
  where
    arity = length premises
    first = Con name (take arity xs)
    rest  = drop arity xs

instance Show Proof where
  show (Con f []) = f
  show (Con f xs) = printf "(%s %s)" f (unwords (map show xs))


-- * Proof search


depthLimitedSearch
  :: (VarClass f Int, UnifyClass f Int, MatchClass (f Int), SubstClass f Int)
     => Int -> f Int -> [Rule f Int] -> [Proof]
depthLimitedSearch depth goal = searchAcc depth (Just Nil) (goalSize, [goal], head)
  where
    goalSize = S.size (allVars goal)

    searchAcc 0     _                     _  _     = [    ]
    searchAcc _     Nothing               _  _     = [    ]
    searchAcc _     (Just _) (_,     [] , p) _     = [p []]
    searchAcc depth (Just s) (n, g : gs , p) rules = concatMap step rules
      where
        step r@Rule{..} = searchAcc (depth - 1) mgu p' rules
          where
            conclusion' = update (+n) conclusion
            mgu         = unifyAcc g conclusion' s
            premises'   = map (update (+n)) premises
            p'          = (n + ruleSize, premises' ++ gs, p . mkProof r)

search :: (VarClass f Int, UnifyClass f Int, MatchClass (f Int), SubstClass f Int)
      => f Int -> [Rule f Int] -> [Proof]
search goal rules = go 1
  where
    go 100   = error "searched up to level 100"
    go depth = let
      result = depthLimitedSearch depth goal rules
      in if null result
         then go (depth + 1)
         else result
