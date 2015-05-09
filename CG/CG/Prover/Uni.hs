module CG.Prover.Uni (Uni,runUni,uni,app,appAll,match) where


import Control.Monad.State (MonadState(..),StateT,runStateT,evalState,liftM2)
import Data.IntMap as IM (lookup,empty,insert,map,foldWithKey)
import Data.Maybe (isJust)
import CG.Prover.Base


match :: (Eq c) => Term c () -> Term c Int -> Bool
match x y = isJust (runUni (uni x' y))
  where
    x'             = evalState (lbl x) fv
    fv             = upperBound y
    lbl (Var   ()) = do i <- get; put (i + 1); return (Var i)
    lbl (Con x xs) = Con x <$> mapM lbl xs


-- This module implements unification, where the both formulas are
-- allowed to contain free variables.
-- The guarantee that we would like to provide is that, at the end of
-- the unification, the user is given a term which contains none of
-- the right argument's variables.


type Uni c a = StateT (VMap c Int) Maybe a

runUni :: Uni c (Term c Int) -> Maybe (Term c Int, VMap c Int)
runUni x = runStateT x IM.empty


uni :: (Eq c) => Term c Int -> Term c Int -> Uni c (Term c Int)
uni (Var i   ) (Var j   )          = flexFlex i j
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


flexFlex :: (Eq c) => Int -> Int -> Uni c (Term c Int)
flexFlex i j | i == j = return (Var i)
flexFlex i j =
  do vm <- get
     case (IM.lookup i vm, IM.lookup j vm) of
      (Just x, Just y) -> if x == y then return x else fail "cannot unify"
      (Just x, _     ) -> do setValue j x; return x
      (_     , Just y) -> do setValue i y; return y
      (_     , _     ) -> let x = Var i in do setValue j x; return x


flexRigid :: (Eq c) => Int -> Term c Int -> Uni c (Term c Int)
flexRigid i x =
  do vm <- get
     case IM.lookup i vm of
      Just y -> if x == y then return x else fail "cannot unify"
      _      -> do setValue i x; return x


setValue :: Int -> Term c Int -> Uni c ()
setValue i x = do vm <- get; put (IM.insert i x (IM.map (app i x) vm))
