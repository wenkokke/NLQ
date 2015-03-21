{-# LANGUAGE GADTs, RecordWildCards, FlexibleContexts #-}
module Prover.Prover where


import Prover.Base
import Prover.Unification hiding ((++),null)

import Data.Maybe (mapMaybe)
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


data Tree a where
  Leaf ::       a  -> Tree a
  Node :: [Tree a] -> Tree a


solve :: (VarClass f Int, UnifyClass f Int, SubstClass f Int)
         => Int -> f Int -> [Rule f Int] -> Tree Proof
solve depth goal = solveAcc depth (goalSize, [goal], head)
  where
    goalSize = S.size (allVars goal)

    solveAcc 0                  _  _     = Node []
    solveAcc _     (_,     [] , p) _     = Leaf (p [])
    solveAcc depth (n, g : gs , p) rules = Node (mapMaybe step rules)
      where
        step r@Rule{..} =
          case unify g (update (+n) conclusion) of
            Nothing  -> Nothing
            Just mgu -> let
              premises' = map (subst mgu . update (+n)) premises
              p'        = (n + ruleSize, premises' ++ gs, p . mkProof r)
              in Just (solveAcc (depth - 1) p' rules)


dfs :: Tree Proof -> [Proof]
dfs (Leaf x ) = [x]
dfs (Node xs) = concatMap dfs xs


bfs :: Tree a -> [a]
bfs tree = go [tree]
  where
    go :: [Tree a] -> [a]
    go [] = []
    go (Leaf x  : xxs) = x : go xxs
    go (Node xs : xxs) = go (xxs ++ xs)


dldfs :: Int -> Tree Proof -> [Proof]
dldfs 0       _   = [ ]
dldfs d (Leaf x ) = [x]
dldfs d (Node xs) = concatMap (dldfs (d - 1)) xs


iddfs :: Tree Proof -> [Proof]
iddfs tree = go 5
  where
    go :: Int -> [Proof]
    go d = if null ret then go (d + 1) else ret
      where
        ret = dldfs d tree
