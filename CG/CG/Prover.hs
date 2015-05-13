{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses,
    UndecidableInstances, DeriveGeneric, RecordWildCards, TupleSections #-}
module CG.Prover (module X,System(..),solve,findAll,findFirst) where


import CG.Prover.Base as X
import CG.Prover.Ins  as X
import Data.Hashable       (Hashable(..))
import Data.HashSet   as S (insert,member,empty)
import Data.Maybe          (mapMaybe)
import Data.Void           (Void)


-- |Search for proofs of the given goals using the given system, using
--  either breadth-first search (for finite systems) or depth-limited
--  interleaved breadth-first search (for infinite systems).
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
solve :: (Operator c, Guardable c, Hashable c, Ord c) => System c -> Int -> [Term c Void] -> [(Term c Void, Term String Void)]
solve System{..} depth goals
  | finite    = concatMap (\goal -> map (goal,) (findAll goal rules)) goals
  | otherwise = findFirst depth goals rules


-- |Search for proofs of the given goal using the gives rules using
--  breadth-first search.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
findAll :: (Operator c, Guardable c, Hashable c, Ord c) => Term c Void -> [Rule c Int] -> [Term String Void]
findAll goal rules = slv [(S.empty,[goal],head)] []
  where
    slv [                    ] [ ] = []
    slv [                    ] acc = slv (reverse acc) []
    slv ((_   ,  [],prf):prfs) acc = prf [] : slv prfs acc
    slv ((seen,g:gs,prf):prfs) acc
      | S.member g seen = slv prfs acc
      | otherwise       = slv prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n grd a ps c) =
          if runGuard grd g
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
findFirst :: (Guardable c, Hashable c, Ord c)
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
        step (Rule n grd a ps c) =
          if runGuard grd g
          then do s <- runIns (ins g c)
                  let prf'  = prf . build n a
                  let seen' | a == 1    = S.insert g seen
                            | otherwise = S.empty
                  ps' <- mapM (subst s) ps
                  return (seen', o, ps' ++ gs, prf')
          else fail ("Cannot apply rule `"++n++"'")


-- |Build a proof by adding a new constructor.
build :: r -> Int -> [Term r Void] -> [Term r Void]
build n a ts = let (xs,ys) = splitAt a ts in Con n xs : ys
