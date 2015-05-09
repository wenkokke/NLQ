{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, DeriveGeneric #-}
module CG.Prover (module X,findAll,findFirst,findAll') where


import Data.Hashable     (Hashable(..))
import Data.HashSet as S (insert,member,empty)
import Data.Maybe        (mapMaybe)
import Data.Void         (Void)

import CG.Prover.Base as X
import CG.Prover.Ins  as X
import CG.Prover.Uni  as X


-- |Search for proofs of the given goal using the gives rules using
--  breadth-first search.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
findAll :: (Hashable c, Ord c) => Term c Void -> [Rule c Int] -> [Term String Void]
findAll goal rules = slv [(S.empty,[goal],head)] []
  where
    slv [                    ] [ ] = []
    slv [                    ] acc = slv (reverse acc) []
    slv ((_   ,  [],prf):prfs) acc = prf [] : slv prfs acc
    slv ((seen,g:gs,prf):prfs) acc
      | S.member g seen = slv prfs acc
      | otherwise       = slv prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n canApply a _ ps c) =
          if canApply g
          then do s <- runIns (ins g c)
                  let prf'  = prf . build n a
                  let seen' | a == 1    = S.insert g seen
                            | otherwise = S.empty
                  ps' <- mapM (subst s) ps
                  return (seen', ps' ++ gs, prf')
          else fail ("Cannot apply rule `"++n++"'")


-- |Search for proofs of the given goal using the gives rules using
--  depth-limited breadth-first search.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
findFirst :: (Hashable c, Ord c)
          => Int           -- ^ Search Depth
          -> [Term c Void] -- ^ Goal Terms
          -> [Rule c Int]  -- ^ Inference rules
          -> [(Term c Void, Term String Void)]
findFirst d goals rules = slv (d + 1) (fmap (\g -> (S.empty,g,[g],head)) goals) []
  where
    slv 0                        _   _ = []
    slv _ [                      ] [ ] = []
    slv d [                      ] acc = slv (d - 1) (reverse acc) []
    slv _ ((_   ,o,  [],prf):_   ) _   = [(o, prf [])]
    slv d ((seen,o,g:gs,prf):prfs) acc
      | S.member g seen = slv d prfs acc
      | otherwise       = slv d prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n canApply a _ ps c) =
          if canApply g
          then do s <- runIns (ins g c)
                  let prf'  = prf . build n a
                  let seen' | a == 1    = S.insert g seen
                            | otherwise = S.empty
                  ps' <- mapM (subst s) ps
                  return (seen', o, ps' ++ gs, prf')
          else fail ("Cannot apply rule `"++n++"'")


-- |Search for proofs of the given goal using the gives rules using
--  breadth-first search.
--  Note: this implementation uses unification, which  means that it
--  is much slower than @findAll@, but the goal term is allowed to
--  contain variables.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
findAll' :: (Hashable c, Ord c) => Term c Int -> [Rule c Int] -> [(Term c Int, Term RuleId Void)]
findAll' goal rules = slv [(S.empty,upperBound goal,goal,[goal],head)] []
  where
    slv [                         ] [ ] = []
    slv [                         ] acc = slv (reverse acc) []
    slv ((_   ,_ ,o,  [],prf):prfs) acc = (o, prf []) : slv prfs acc
    slv ((seen,fv,o,g:gs,prf):prfs) acc
      | S.member g seen = slv prfs acc
      | otherwise       = slv prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n canApply a fv' ps c) =
          if canApply g then do
            let c'    = fmap (+fv) c
            (_,s) <- runUni (uni g c')
            let prf'  = prf . build n a
            let seen' = if a == 1 then S.insert g seen else S.empty
            let gs'   = map (appAll s) gs
            let ps'   = map (appAll s . fmap (+fv)) ps
            return (seen', fv + fv', appAll s o, ps' ++ gs', prf')
          else fail ("Cannot apply rule `"++n++"'")


build :: r -> Int -> [Term r Void] -> [Term r Void]
build n a ts = let (xs,ys) = splitAt a ts in Con n xs : ys
