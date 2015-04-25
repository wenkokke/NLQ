module Logic.Prover.Uni (Uni,runUni,uni,app,appAll) where


import Control.Monad.State (MonadState(..),StateT,runStateT,liftM2)
import Data.IntMap as IM (lookup,empty,insert,map,foldWithKey)
import Logic.Prover.Base


-- This module implements unification, where the both formulas are
-- allowed to contain free variables.
-- The guarantee that we would like to provide is that, at the end of
-- the unification, the user is given a term which contains none of
-- the right argument's variables.


type Uni c a = StateT (VMap c Int) Maybe a

runUni :: Uni c (Term c Int) -> Maybe (Term c Int, VMap c Int)
runUni x = runStateT x IM.empty


uni :: (Eq c) => Term c Int -> Term c Int -> Uni c (Term c Int)
uni      x     (Var j   )          = flexRigid j x
uni (Var i   )      y              = flexRigid i y
uni (Con x xs) (Con y ys) | x == y = Con x <$> uniAll xs ys
uni      _          _              = fail "cannot unify"


uniAll :: (Eq c) => [Term c Int] -> [Term c Int] -> Uni c [Term c Int]
uniAll    []     []  = return []
uniAll (x:xs) (y:ys) = liftM2 (:) (uni x y) (uniAll xs ys)
uniAll  _      _     = fail "cannot unify"


app :: Int -> Term c Int -> Term c Int -> Term c Int
app i x   (Con y ys) = Con y (app i x <$> ys)
app i x y@(Var j   ) = if i == j then x else y


appAll :: VMap c Int -> Term c Int -> Term c Int
appAll vm = IM.foldWithKey (\i x -> (. app i x)) id vm


flexRigid :: (Eq c) => Int -> Term c Int -> Uni c (Term c Int)
flexRigid i x =
  do vm <- get
     case IM.lookup i vm of
      Just y -> if x == y then return x else fail "cannot unify"
      _      -> do put (IM.insert i x (IM.map (app i x) vm)); return x
