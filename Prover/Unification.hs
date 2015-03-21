{-# LANGUAGE GADTs, MultiParamTypeClasses, FlexibleInstances, ScopedTypeVariables, FlexibleContexts, UndecidableInstances #-}
module Prover.Unification where


import Prover.Base

import Text.Printf (printf)
import Prelude hiding ((++),null)


-- * Substitutions

data Subst f n where
  Nil  :: Subst f n
  Down :: Subst f n             -> Subst (Term o f) n
  Snoc :: Subst f n -> n -> f n -> Subst         f  n

instance (Show n) => (Show (Subst Name n)) where
  show  Nil           = "[]"
  show (Snoc Nil x t) = printf "[%s ⟼ %s]"   (show x) (show t)
  show (Snoc acc x t) = printf "[%s ⟼ %s]%s" (show x) (show t) (show acc)

instance (Show (Subst f n), Show (Term o f n), Show n) => Show (Subst (Term o f) n) where
  show  Nil                  = "[]"
  show (Down       acc     ) = show acc
  show (Snoc       Nil  x t) = printf "[%s ⟼ %s]"   (show x) (show t)
  show (Snoc (Down Nil) x t) = printf "[%s ⟼ %s]"   (show x) (show t)
  show (Snoc       acc  x t) = printf "[%s ⟼ %s]%s" (show x) (show t) (show acc)


null :: Subst f n -> Bool
null Nil      = True
null (Down s) = null s
null _        = False

down :: Subst (Term o f) n -> Subst f n
down = fst . split

split :: Subst (Term o f) n -> (Subst f n , Subst (Term o f) n -> Subst (Term o f) n)
split  Nil         = (Nil , id)
split (Down s    ) = (s   , id)
split (Snoc s x f) = case split s of (s', up) -> (s', \s'' -> Snoc (up s'') x f)

replaceAll :: (Eq n) => Subst (Term o f) n -> n -> Term o f n
replaceAll (Snoc s x f) y = if x == y then f else replaceAll s y
replaceAll _            y = Var y


class SubstClass f n where
  (++) :: Subst f n -> Subst f n -> Subst f n
  subst :: Subst f n -> f n -> f n

instance SubstClass Name n where
  Nil         ++ ys = ys
  Snoc xs x t ++ ys = Snoc (xs ++ ys) x t
  subst _ x = x

instance (Eq n, SubstClass f n) => SubstClass (Term o f) n where
  xs ++ ys = case (split xs, split ys) of
    ((Nil, xs2), (ys1, ys2)) -> xs2 (ys2 (Down         ys1 ))
    ((xs1, xs2), (Nil, ys2)) -> xs2 (ys2 (Down  xs1        ))
    ((xs1, xs2), (ys1, ys2)) -> xs2 (ys2 (Down (xs1 ++ ys1)))

  subst s = subst'
    where
      s'  = down s
      rep = replaceAll s
      subst' (Var  x ) = rep x
      subst' (El   x ) = El (subst s' x)
      subst' (Op f xs) = Op f (map subst' xs)



-- * Occurs Check

class Occurs f n where
  occursIn :: n -> f n -> Maybe ()

instance Occurs Name n where
  occursIn _ _ = return ()

instance (Eq n, Show n, Occurs f n) => Occurs (Term o f) n where
  x `occursIn` (Var  y )
    | x == y    = Nothing
    | otherwise = Just ()
  x `occursIn` (El   y ) = x `occursIn` y
  x `occursIn` (Op _ ys) = mapM_ (x `occursIn`) ys



-- * Unification

class UnifyClass f n where
  unify :: f n -> f n -> Maybe (Subst f n)
  unify x y = unifyAcc x y Nil

  unifyAcc :: f n -> f n -> Subst f n -> Maybe (Subst f n)

  unifyAccChildren :: [f n] -> [f n] -> Subst f n -> Maybe (Subst f n)
  unifyAccChildren      []       []  acc = Just acc
  unifyAccChildren (x : xs) (y : ys) acc = unifyAcc x y acc >>= unifyAccChildren xs ys


instance (Eq n) => UnifyClass Name n where
  unifyAcc x y s
    | x == y    = Just s
    | otherwise = Nothing

instance (Eq n, Eq o, UnifyClass f n, SubstClass f n) => UnifyClass (Term o f) n where
  unifyAcc (Op f xs) (Op g ys) acc = if f == g then unifyAccChildren xs ys acc else Nothing
  unifyAcc (El   x ) (El   y ) acc = case split acc of (acc', up) -> fmap (up . Down) (unifyAcc x y acc')
  unifyAcc       x   (Var  y ) Nil = Just (Snoc Nil y x)
  unifyAcc (Var  x )       y   Nil = Just (Snoc Nil x y)
  unifyAcc       x         y   acc
    | null acc  = Nothing
    | otherwise = fmap (acc ++) (unifyAcc (subst acc x) (subst acc y) Nil)
