{-# LANGUAGE GADTs, KindSignatures, RecordWildCards, MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}
module Base where


import Control.Monad.Supply
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map,(!))
import qualified Data.Map as M
import qualified Data.Foldable as F


-- * Term definition

newtype Name n = Name String
  deriving (Eq)

instance (Show n) => Show (Name n) where
  show (Name x) = show x


data Term (o :: *) (f :: * -> *) (n :: *) :: * where
  Var :: !  n                     -> Term o f n
  El  :: ! (f n)                  -> Term o f n
  Op  :: !  o    -> ![Term o f n] -> Term o f n
  deriving (Eq)


-- * Variable utilities

class VarClass f n where
  update  :: (n -> m) -> f n -> f m
  allVars :: (Ord n) => f n -> Set n

instance VarClass Name n where
  update  _ (Name x) = Name x
  allVars   (Name _) = S.empty

instance (VarClass f n) => VarClass (Term o f) n where
  update u (Var  x ) = Var (u x)
  update u (El   x ) = El (update u x)
  update u (Op f xs) = Op f (map (update u) xs)

  allVars  (Var  x ) = S.singleton x
  allVars  (El   x ) = allVars x
  allVars  (Op _ xs) = foldr (\x y -> S.union (allVars x) y) S.empty xs


mkTable :: (Ord n) => Set n -> Map n Int
mkTable xs = evalSupply (F.foldrM (\x m -> supply >>= \i -> return (M.insert x i m)) M.empty xs) [1..]

index :: (Ord n, VarClass f n) => f n -> f Int
index x = update (table !) x
  where
    table = mkTable (allVars x)


-- * Rule definition

type RuleName = String

data Rule f n = Rule
  { name       :: !RuleName
  , ruleSize   :: !Int
  , premises   :: ![f n]
  , conclusion :: !(f n)
  }
  deriving (Eq)

instance (Show (f n), Show n) => Show (Rule f n) where
  showsPrec _ Rule{..} =
      showString "( "
    . showList premises
    . showString " ⟶ "
    . shows conclusion
    . showString " ) \""
    . showString name
    . showString "\"\n"


-- * Rule construction syntax

infixr 1 ⟶

(⟶) :: (VarClass f n, Ord n) => [f n] -> f n -> String -> Rule f Int
(⟶) p c n = Rule { name = n , ruleSize = ruleSize, premises = map index p , conclusion = index c }
  where
    ruleVars = S.union (allVars c) (foldr (\x y -> S.union (allVars x) y) S.empty p)
    ruleSize = S.size ruleVars
    table    = mkTable ruleVars
    index    = update (table !)
