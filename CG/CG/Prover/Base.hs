{-# LANGUAGE GADTs, RankNTypes, FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveGeneric #-}
module CG.Prover.Base where

import Control.Monad.State (MonadState(..),evalState)
import Control.DeepSeq (NFData)
import Data.Hashable (Hashable)
import Data.IntMap as IM (IntMap,lookup)
import Data.Map as M (lookup,empty,insert)
import Data.Void (Void,absurd)
import Data.Void.Unsafe (unsafeVacuous)
import GHC.Generics


-- * Terms

data Term c v where
  Var :: ! v               -> Term c v
  Con :: ! c -> [Term c v] -> Term c v
  deriving (Eq,Ord,Generic)


instance Functor (Term c) where
  fmap f (Var i)    = Var (f i)
  fmap f (Con x xs) = Con x (map (fmap f) xs)


upperBound :: Term c Int -> Int
upperBound (Var i   ) = i
upperBound (Con _ xs) =
  let vs = map upperBound xs in if null vs then 0 else maximum vs


castVar :: Term c Void -> Term c v
castVar = unsafeVacuous


instance (Hashable c, Hashable v) => Hashable (Term c v)
instance (NFData   c, NFData   v) => NFData (Term c v)


instance (Show v) => Show (Term String v) where
  showsPrec _ (Var i)    = shows i
  showsPrec _ (Con f []) = showString f
  showsPrec p (Con f xs) =
    showParen (p >= 1) $ showString f . showSeq (showsPrec 1) xs
    where
      showSeq _  []     = id
      showSeq ss (x:xs) = showChar ' ' . ss x . showSeq ss xs


-- * Rules

type RuleId = String

data Rule c v = Rule
  { name       :: ! RuleId
  , guard      :: forall v'. Term c v' -> Bool
  , arity      :: ! Int
  , numVars    :: ! Int
  , premises   :: ! [Term c v]
  , conclusion :: ! (Term c v)
  }

mkRule :: [Term c String] -> Term c String -> RuleId -> Rule c Int
mkRule ps c n = Rule n (const True) (length ps) (upperBound c') ps' c'
  where

    (c' : ps') = evalState (mapM lbl (c : ps)) (0, M.empty)

    lbl (Var x) = do (i, vm) <- get
                     case M.lookup x vm of
                      Just j -> return (Var j)
                      _      -> do put (i + 1, M.insert x i vm); return (Var i)
    lbl (Con x xs) = fmap (Con x) (mapM lbl xs)


instance (Show c, Show v, Show (Term c v)) => Show (Rule c v) where
  showsPrec _ (Rule n _ _ _ ps c) =
    showParen True (showList ps . showString " ⟶ " . shows c) . showChar ' ' . showString n


-- * Substitutions

type VMap c v = IntMap (Term c v)


-- |Apply the given variable map to a given term. Note: the variable
--  map has to contain a term for every variable used in the given
--  term. The resulting term will be variable-free.
subst :: VMap c Void -> Term c Int -> Maybe (Term c Void)
subst s = app where

  app (Con x xs) = Con x <$> mapM app xs
  app (Var i   ) = IM.lookup i s
