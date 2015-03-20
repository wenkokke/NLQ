{-# LANGUAGE GADTs #-}
module Match where


import Control.Monad
import Control.Monad.Except
import Data.Map (Map)
import qualified Data.Map as M

import Base


class Match a where
  match :: a -> a -> Bool


instance Match Formula where
  match (FVar  _)  _          = True
  match _          (FVar  _)  = True
  match (FOp f xs) (FOp g ys) = f == g && and (zipWith match xs ys)

instance Match Structure where
  match (SVar  _)  _          = True
  match _          (SVar  _)  = True
  match (SEl   x)  (SEl   y)  = x == y
  match (SOp f xs) (SOp g ys) = f == g && and (zipWith match xs ys)
  match _          _          = False

instance Match Judgement where
  match (Struct x y) (Struct z w) = match x z && match y w
  match (FocusL a y) (FocusL c w) = match a c && match y w
  match (FocusR x b) (FocusR z d) = match x z && match b d
  match _            _            = False



data Subst where
  Nil   :: Subst
  FSnoc :: String -> Formula   -> Subst -> Subst
  SSnoc :: String -> Structure -> Subst -> Subst
  deriving (Eq,Show)


class Unify a where
  unifyAcc :: a -> a -> Subst -> Except String Subst
  unify    :: a -> a          -> Except String Subst
  unify x y = unifyAcc x y Nil


fOccursIn :: String -> Formula -> Except String ()
fOccursIn _ (FVar  _) = return ()
fOccursIn x f = go f
  where
    go (FVar  y )
      | x == y    = throwError (show x ++ " occurs in " ++ show y)
      | otherwise = return ()
    go (FOp _ ys) = mapM_ go ys


instance Unify Formula where
  unifyAcc   (FVar  x)  y            s = x `fOccursIn` y >> return (FSnoc x y s)
  unifyAcc x              (FVar  y ) s = y `fOccursIn` x >> return (FSnoc y x s)
  unifyAcc x@(FOp f xs) y@(FOp g ys) s
    | f == g    = go xs ys
    | otherwise = throwError ("cannot unify " ++ show x ++ " and " ++ show y)
    where
      go (x : []) (y : []) = unifyAcc x y s
      go (x : xs) (y : ys) = go xs ys >>= \s' -> unifyAcc x y s'


sOccursIn :: String -> Structure -> Except String ()
sOccursIn _ (SVar  _) = return ()
sOccursIn x f = go f
  where
    go (SVar  y )
      | x == y    = throwError (show x ++ " occurs in " ++ show y)
      | otherwise = return ()
    go (SEl   _ ) = return ()
    go (SOp _ ys) = mapM_ go ys

instance Unify Structure where
  unifyAcc (SVar  x)    y            s = x `sOccursIn` y >> return (SSnoc x y s)
  unifyAcc x              (SVar y)   s = y `sOccursIn` x >> return (SSnoc y x s)
  unifyAcc x@(SEl _)    y@(SEl  _)   s
    | x == y    = return s
    | otherwise = throwError ("cannot unify " ++ show x ++ " and " ++ show y)
  unifyAcc x@(SOp f xs) y@(SOp g ys) s
    | f == g    = go xs ys
    | otherwise = throwError ("cannot unify" ++ show x ++ " and " ++ show y)
    where
      go (x : []) (y : []) = unifyAcc x y s
      go (x : xs) (y : ys) = go xs ys >>= \s' -> unifyAcc x y s'
  unifyAcc x            y            s = throwError ("cannot unify" ++ show x ++ " and " ++ show y)


instance Unify Judgement where
  unifyAcc (Struct x y) (Struct z w) s = unifyAcc x z s >>= \s' -> unifyAcc y w s'
  unifyAcc (FocusL a y) (FocusL c w) s = unifyAcc a c s >>= \s' -> unifyAcc y w s'
  unifyAcc (FocusR x b) (FocusR z d) s = unifyAcc x z s >>= \s' -> unifyAcc b d s'
  unifyAcc x            y            _ = throwError ("cannot unify" ++ show x ++ " and " ++ show y)
