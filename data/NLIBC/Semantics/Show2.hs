{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             FlexibleInstances, MultiParamTypeClasses, PatternSynonyms #-}
module NLIBC.Semantics.Show2 (Repr(..),show2) where


import Prelude hiding ((!!))
import Control.Monad.State
import Data.Map (Map)
import qualified Data.Map as M
import Data.Singletons (fromSing)
import NLIBC.Syntax (Prf(..),Sequent(..))
import NLIBC.Semantics (Nat(..),SNat(..),(:!!),(!!),Sem(..),HI,eta)
import Text.Printf (printf)



data Repr (ts :: [*]) (t :: *) where
  Var  :: SNat n -> Repr ts (ts :!! n)
  Con  :: String -> Repr ts t
  Abs  :: Repr (t1 ': ts) t2 -> Repr ts (t1 -> t2)
  App  :: Repr ts (t1 -> t2) -> Repr ts t1 -> Repr ts t2
  Top  :: Repr ts ()
  Pair :: Repr ts t1 -> Repr ts t2 -> Repr ts (t1, t2)
  P1   :: Repr ts (t1, t2) -> Repr ts t1
  P2   :: Repr ts (t1, t2) -> Repr ts t2

instance Sem Repr where
  var  = Var
  abs  = Abs
  app  = App
  top  = Top
  pair = Pair
  p1   = P1
  p2   = P2

data ReprU where
  VarU  :: Name -> ReprU
  ConU  :: Name -> ReprU
  AbsU  :: Name -> ReprU -> ReprU
  AppU  :: ReprU -> ReprU -> ReprU
  TopU  :: ReprU
  PairU :: ReprU -> ReprU -> ReprU
  P1U   :: ReprU -> ReprU
  P2U   :: ReprU -> ReprU


type Name = String


freshNames :: [Name]
freshNames = map (('x':).show) [1..]


forget :: Repr ts t -> ReprU
forget x = evalState (go x) ([],freshNames)
  where
    go :: Repr ts t -> State ([String],[String]) ReprU
    go (Var n)    = do (env,_) <- get; return $ VarU (env !! fromSing n)
    go (Con c)    = return $ ConU c
    go (Abs u)    = do (env,x:xs) <- get
                       put (x:env,xs)
                       u' <- go u
                       (x:env,xs) <- get
                       put (env,xs)
                       return $ AbsU x u'
    go (App u v)  = AppU <$> go u <*> go v
    go  Top       = return TopU
    go (Pair u v) = PairU <$> go u <*> go v
    go (P1 u)     = P1U <$> go u
    go (P2 u)     = P2U <$> go u


show2 :: Repr '[] (HI x) -> Prf (x :⊢ y) -> String
show2 x f = show (evalState (relabel (normalise (forget (eta f `App` x)))) (M.empty,freshNames))
  where
    relabel :: ReprU -> State (Map Name Name,[Name]) ReprU
    relabel (VarU  y)   = do (env,x:xs) <- get
                             case M.lookup y env of
                               Just  z -> return (VarU z)
                               Nothing -> do put (M.insert y x env,xs)
                                             return (VarU x)
    relabel (AbsU  y u) = do (env,x:xs) <- get
                             let z = M.lookup y env
                             put (M.insert y x env,xs)
                             u' <- relabel u
                             (env,xs) <- get
                             put (M.alter (const z) y env,xs)
                             return (AbsU x u')
    relabel (AppU  u v) = AppU  <$> relabel u <*> relabel v
    relabel (PairU u v) = PairU <$> relabel u <*> relabel v
    relabel (P1U   u)   = P1U   <$> relabel u
    relabel (P2U   u)   = P2U   <$> relabel u
    relabel u           = return u

    subst :: Name -> ReprU -> ReprU -> ReprU
    subst x t (VarU  y)   | x == y = t
    subst x t (AbsU  y u) | x /= y = AbsU  y             (subst x t u)
    subst x t (AppU  u v)          = AppU  (subst x t u) (subst x t v)
    subst x t (PairU u v)          = PairU (subst x t u) (subst x t v)
    subst x t (P1U   u)            = P1U   (subst x t u)
    subst x t (P2U   u)            = P2U   (subst x t u)
    subst x t u                    = u

    normalise :: ReprU -> ReprU
    normalise (VarU x)    = VarU x
    normalise (ConU c)    = ConU c
    normalise (AbsU x u)  = AbsU x (normalise u)
    normalise (AppU u v)  = case normalise u of
      AbsU x w -> normalise (subst x (normalise v) w)
      w        -> AppU w (normalise v)
    normalise  TopU       = TopU
    normalise (PairU u v) = PairU (normalise u) (normalise v)
    normalise (P1U u)     = case normalise u of
      PairU w _ -> w
      w         -> P1U w
    normalise (P2U u)     = case normalise u of
      PairU _ w -> w
      w         -> P2U w


instance Show (Repr ts t) where
  show r = show (forget r)


pattern Con1U f x1                = AppU (ConU f) x1
pattern Con2U f x1 x2             = AppU (Con1U f x1) x2
pattern Con3U f x1 x2 x3          = AppU (Con2U f x1 x2) x3
pattern Con4U f x1 x2 x3 x4       = AppU (Con3U f x1 x2 x3) x4
pattern Con5U f x1 x2 x3 x4 x5    = AppU (Con4U f x1 x2 x3 x4) x5
pattern Con6U f x1 x2 x3 x4 x5 x6 = AppU (Con5U f x1 x2 x3 x4 x5) x6

pattern Var1U f x1                = AppU (VarU  f) x1
pattern Var2U f x1 x2             = AppU (Var1U f x1) x2
pattern Var3U f x1 x2 x3          = AppU (Var2U f x1 x2) x3
pattern Var4U f x1 x2 x3 x4       = AppU (Var3U f x1 x2 x3) x4
pattern Var5U f x1 x2 x3 x4 x5    = AppU (Var4U f x1 x2 x3 x4) x5
pattern Var6U f x1 x2 x3 x4 x5 x6 = AppU (Var5U f x1 x2 x3 x4 x5) x6

pattern ForallU x u = Con1U "∀" (AbsU x u)
pattern ExistsU x u = Con1U "∃" (AbsU x u)
pattern a :∧ b      = Con2U "∧" a b
pattern a :⊃ b      = Con2U "⊃" a b
pattern a :≡ b      = Con2U "≡" a b

showArgs :: Show a => [a] -> ShowS
showArgs []     s = "()" ++ s
showArgs (x:xs) s = '(' : shows x (showl xs)
  where
    showl []     = ')' : s
    showl (y:ys) = ',' : shows y (showl ys)

instance Show ReprU where
  showsPrec d (ForallU x u) =
    showParen (d > 1) $ showChar '∀' . showString x . showChar '.' . showsPrec 2 u
  showsPrec d (ExistsU x u) =
    showParen (d > 1) $ showChar '∃' . showString x . showChar '.' . showsPrec 2 u
  showsPrec d (AbsU  x u)   =
    showParen (d > 1) $ showChar 'λ' . showString x . showChar '.' . showsPrec 2 u

  showsPrec d (u :∧ v)      =
    showParen (d > 2) $ showsPrec 2 u . showString " ∧ " . showsPrec 3 v
  showsPrec d (u :⊃ v)      =
    showParen (d > 4) $ showsPrec 4 u . showString " ⊃ " . showsPrec 5 v
  showsPrec d (u :≡ v)      =
    showParen (d > 4) $ showsPrec 4 u . showString " ≡ " . showsPrec 5 v

  showsPrec d (Con1U f x1)                = showString f . showArgs [x1]
  showsPrec d (Con2U f x1 x2)             = showString f . showArgs [x1,x2]
  showsPrec d (Con3U f x1 x2 x3)          = showString f . showArgs [x1,x2,x3]
  showsPrec d (Con4U f x1 x2 x3 x4)       = showString f . showArgs [x1,x2,x3,x4]
  showsPrec d (Con5U f x1 x2 x3 x4 x5)    = showString f . showArgs [x1,x2,x3,x4,x5]
  showsPrec d (Con6U f x1 x2 x3 x4 x5 x6) = showString f . showArgs [x1,x2,x3,x4,x5,x6]

  showsPrec d (Var1U f x1)                = showString f . showArgs [x1]
  showsPrec d (Var2U f x1 x2)             = showString f . showArgs [x1,x2]
  showsPrec d (Var3U f x1 x2 x3)          = showString f . showArgs [x1,x2,x3]
  showsPrec d (Var4U f x1 x2 x3 x4)       = showString f . showArgs [x1,x2,x3,x4]
  showsPrec d (Var5U f x1 x2 x3 x4 x5)    = showString f . showArgs [x1,x2,x3,x4,x5]
  showsPrec d (Var6U f x1 x2 x3 x4 x5 x6) = showString f . showArgs [x1,x2,x3,x4,x5,x6]

  showsPrec d (AppU  u v)   =
    showParen (d > 10) $ showsPrec 10 u . showChar ' ' . showsPrec 11 v

  showsPrec _  TopU     = showString "()"
  showsPrec _ (VarU  x) = showString x
  showsPrec _ (ConU  c) = showString c

  showsPrec d (PairU u v) = showArgs [u,v]
  showsPrec d (P1U   u)   = showString "π₁" . showArgs [u]
  showsPrec d (P2U   u)   = showString "π₂" . showArgs [u]
