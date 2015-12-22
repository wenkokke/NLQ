{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, TypeFamilies,
             FlexibleInstances, MultiParamTypeClasses, PatternSynonyms #-}
module NLIBC.Semantics.Show2 (Repr(..),show2) where


import           Prelude hiding ((!!))
import           Control.Monad.State
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Singletons (fromSing)
import           NLIBC.Semantics (Nat(..),SNat(..),(:!!),(!!),Sem(..),HI,HO)
import           Text.Printf (printf)


data Repr (ts :: [*]) (t :: *) where
  Var    :: SNat n -> Repr ts (ts :!! n)
  Con    :: String -> Repr ts t
  Abs    :: Repr (t1 ': ts) t2 -> Repr ts (t1 -> t2)
  App    :: Repr ts (t1 -> t2) -> Repr ts t1 -> Repr ts t2
  Unit   :: Repr ts ()
  Pair   :: Repr ts t1 -> Repr ts t2 -> Repr ts (t1, t2)
  CaseOf :: Repr ts (t1, t2) -> Repr (t1 ': t2 ': ts) t3 -> Repr ts t3


instance Sem Repr where
  var    = Var
  abs    = Abs
  app    = App
  unit   = Unit
  pair   = Pair
  caseof = CaseOf


data ReprU where
  VarU    :: Name -> ReprU
  ConU    :: Name -> ReprU
  AbsU    :: Name -> ReprU -> ReprU
  AppU    :: ReprU -> ReprU -> ReprU
  UnitU   :: ReprU
  PairU   :: ReprU -> ReprU -> ReprU
  CaseOfU :: ReprU -> (Name, Name) -> ReprU -> ReprU


type Name = String


freshNames :: [Name]
freshNames = map (('x':).show) [1..]


forget :: Repr ts t -> ReprU
forget x = evalState (go x) ([],freshNames)
  where
    go :: Repr ts t -> State ([String],[String]) ReprU
    go (Var n)      = do (env,_) <- get; return $ VarU (env !! fromSing n)
    go (Con c)      = return $ ConU c
    go (Abs u)      = do (env,x:xs) <- get
                         put (x:env,xs)
                         u' <- go u
                         (x:env,xs) <- get
                         put (env,xs)
                         return $ AbsU x u'
    go (App u v)    = AppU <$> go u <*> go v
    go  Unit        = return UnitU
    go (Pair u v)   = PairU <$> go u <*> go v
    go (CaseOf u v) = do u' <- go u
                         (env,x:y:xs) <- get
                         put (x:y:env,xs)
                         v' <- go v
                         (x:y:env,xs) <- get
                         put (env,xs)
                         return $ CaseOfU u' (x,y) v'


show2 :: Repr '[] x -> Repr '[] (x -> y) -> String
show2 x f = show (evalState (relabel (normalise (forget (f `App` x)))) (M.empty,freshNames))
  where
    relabel :: ReprU -> State (Map Name Name,[Name]) ReprU
    relabel (VarU  y)              = do (env,x:xs) <- get
                                        case M.lookup y env of
                                          Just  z -> return (VarU z)
                                          Nothing -> do put (M.insert y x env,xs)
                                                        return (VarU x)
    relabel (AbsU  x u)            = do (env,newX:xs) <- get
                                        let oldX = M.lookup x env
                                        put (M.insert x newX env,xs)
                                        u' <- relabel u
                                        (env,xs) <- get
                                        put (M.alter (const oldX) x env,xs)
                                        return (AbsU newX u')
    relabel (AppU  u v)            = AppU  <$> relabel u <*> relabel v
    relabel (PairU u v)            = PairU <$> relabel u <*> relabel v
    relabel (CaseOfU u (x,y) v)    = do u' <- relabel u
                                        (env,newX:newY:xs) <- get
                                        let oldX = M.lookup x env
                                        let oldY = M.lookup y env
                                        put (M.insert x newX (M.insert y newY env),xs)
                                        v' <- relabel v
                                        put ( M.alter (const oldX) x
                                            . M.alter (const oldY) y $ env,xs)
                                        return (CaseOfU u' (newX,newY) v')
    relabel u                      = return u

    subst :: Name -> ReprU -> ReprU -> ReprU
    subst x t (VarU  y)   | x == y  = t
    subst x t (AbsU  y u) | x /= y  = AbsU y (subst x t u)
    subst x t (AppU  u v)           = AppU  (subst x t u) (subst x t v)
    subst x t (PairU u v)           = PairU (subst x t u) (subst x t v)
    subst x t (CaseOfU u (y,z) v)
      | x `notElem` [y,z]           = CaseOfU (subst x t u) (y,z) (subst x t v)
      | otherwise                   = CaseOfU (subst x t u) (y,z) v
    subst x t u                     = u

    normalise :: ReprU -> ReprU
    normalise (VarU x)            = VarU x
    normalise (ConU c)            = ConU c
    normalise (AbsU x u)          = AbsU x (normalise u)
    normalise (AppU u v)          = case normalise u of
      AbsU x w -> normalise (subst x (normalise v) w)
      w        -> AppU w (normalise v)
    normalise  UnitU              = UnitU
    normalise (PairU u v)         = PairU (normalise u) (normalise v)
    normalise (CaseOfU u (x,y) v) = case normalise u of
      PairU u1 u2 -> normalise (subst x (normalise u1) (subst y (normalise u2) v))
      u'          -> CaseOfU u' (x,y) (normalise v)


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

  showsPrec _  UnitU    = showString "()"
  showsPrec _ (VarU  x) = showString x
  showsPrec _ (ConU  c) = showString c

  showsPrec d (PairU u v)         = showArgs [u,v]
  showsPrec d (CaseOfU u (x,y) v) =
    showParen (d > 1) $ showString "case " . shows u
                      . showString (" of (" ++ x ++ ", " ++ y ++ ") → ")
                      . showsPrec 2 v
