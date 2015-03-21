{-# LANGUAGE GADTs, MultiParamTypeClasses, FunctionalDependencies, TypeSynonymInstances, FlexibleInstances #-}
module Prover.LambekGrishin.Base where


import Prover.Base


-- * Base operators

data Oper where
  Prod :: Oper
  ImpR :: Oper
  ImpL :: Oper
  Plus :: Oper
  SubL :: Oper
  SubR :: Oper
  deriving (Eq)

data Sequent where
  Struct :: Sequent
  FocusL :: Sequent
  FocusR :: Sequent
  deriving (Eq)


-- * Base data types

type Formula   n =                          Term Oper Name   n
type Structure n =               Term Oper (Term Oper Name)  n
type Judgement n = Term Sequent (Term Oper (Term Oper Name)) n


-- * Show functions for judgements

instance (Show n) => Show (Formula n) where
  showsPrec _ (Var x)          = shows x
  showsPrec _ (El  x)          = shows x
  showsPrec p (Op Prod [x, y]) = showParen (p > 6) (showsPrec 6 x . showString " ⊗ " . showsPrec 6 y)
  showsPrec p (Op ImpR [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇒ " . showsPrec 5 y)
  showsPrec p (Op ImpL [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇐ " . showsPrec 5 y)
  showsPrec p (Op Plus [x, y]) = showParen (p > 6) (showsPrec 6 x . showString " ⊕ " . showsPrec 6 y)
  showsPrec p (Op SubL [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇚ " . showsPrec 5 y)
  showsPrec p (Op SubR [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇛ " . showsPrec 5 y)

instance (Show n) => Show (Structure n) where
  showsPrec _ (Var x)          = shows x
  showsPrec _ (El x)           = shows x
  showsPrec p (Op Prod [x, y]) = showParen (p > 4) (showsPrec 4 x . showString " ·⊗· " . showsPrec 4 y)
  showsPrec p (Op ImpR [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ·⇒· " . showsPrec 3 y)
  showsPrec p (Op ImpL [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ·⇐· " . showsPrec 3 y)
  showsPrec p (Op Plus [x, y]) = showParen (p > 4) (showsPrec 4 x . showString " ·⊕· " . showsPrec 4 y)
  showsPrec p (Op SubL [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ·⇚· " . showsPrec 3 y)
  showsPrec p (Op SubR [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ·⇛· " . showsPrec 3 y)

instance (Show n) => Show (Judgement n) where
  showsPrec _ (Op Struct [El x, El y]) =                   shows x . showString   " ⊢ "   . shows y
  showsPrec _ (Op FocusL [El a, El y]) = showString "[ " . shows a . showString " ] ⊢ "   . shows y
  showsPrec _ (Op FocusR [El x, El b]) =                   shows x . showString   " ⊢ [ " . shows b . showString " ]"



-- * Conversions to `Formula`, `Structure` and `Judgement`

class IsFormula   n a   | a   -> n where toFormula   :: a -> Formula   n
class IsStructure n a   | a   -> n where toStructure :: a -> Structure n
class IsJudgement n a b | a b -> n where (⊢)         :: a -> b -> Judgement n


instance IsFormula   n (Formula   n) where toFormula   = id
instance IsStructure n (Structure n) where toStructure = id
instance IsStructure n (Formula   n) where toStructure = El


instance IsJudgement n (Structure n) (Structure n) where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement n (Formula   n) (Formula   n) where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement n (Structure n) (Formula   n) where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement n (Formula   n) (Structure n) where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement n [Formula   n] (Structure n) where x ⊢ y = Op FocusL [El (El (toFormula (head x))) , El     (toStructure     y  )]
instance IsJudgement n (Structure n) [Formula   n] where x ⊢ y = Op FocusR [El     (toStructure     x  ) , El (El (toFormula (head y)))]
instance IsJudgement n [Formula   n] (Formula   n) where x ⊢ y = Op FocusL [El (El (toFormula (head x))) , El     (toStructure     y  )]
instance IsJudgement n (Formula   n) [Formula   n] where x ⊢ y = Op FocusR [El     (toStructure     x  ) , El (El (toFormula (head y)))]


instance IsFormula String String where
  toFormula x
    | x `elem` ["A","B","C","D"] = Var x
    | otherwise                  = El (Name x)

instance IsStructure String String where
  toStructure x
    | x `elem` ["A","B","C","D"] = El (Var x)
    | x `elem` ["X","Y","Z","W"] = Var x
    | otherwise                  = El (El (Name x))


instance IsJudgement String (Structure String)            String  where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement String            String  (Structure String) where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement String (Formula   String)            String  where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement String            String  (Formula   String) where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement String            String             String  where x ⊢ y = Op Struct [El     (toStructure     x  ) , El     (toStructure     y  )]
instance IsJudgement String [Formula   String]            String  where x ⊢ y = Op FocusL [El (El (toFormula (head x))) , El     (toStructure     y  )]
instance IsJudgement String            String  [Formula   String] where x ⊢ y = Op FocusR [El     (toStructure     x  ) , El (El (toFormula (head y)))]
instance IsJudgement String [          String] (Structure String) where x ⊢ y = Op FocusL [El (El (toFormula (head x))) , El     (toStructure     y  )]
instance IsJudgement String (Structure String) [          String] where x ⊢ y = Op FocusR [El     (toStructure     x  ) , El (El (toFormula (head y)))]
instance IsJudgement String [          String] (Formula   String) where x ⊢ y = Op FocusL [El (El (toFormula (head x))) , El     (toStructure     y  )]
instance IsJudgement String (Formula   String) [          String] where x ⊢ y = Op FocusR [El     (toStructure     x  ) , El (El (toFormula (head y)))]
instance IsJudgement String [          String]            String  where x ⊢ y = Op FocusL [El (El (toFormula (head x))) , El     (toStructure     y  )]
instance IsJudgement String            String  [          String] where x ⊢ y = Op FocusR [El     (toStructure     x  ) , El (El (toFormula (head y)))]



-- * Syntactic sugar for writing `Formula`, `Structure` and `Judgement`

infixr 6  ⊗
infixr 6  ⊕
infixr 5  ⇒
infixr 5  ⇛
infixl 5  ⇐
infixl 5  ⇚
infixr 4 ·⊗·
infixr 4 ·⊕·
infixr 3 ·⇒·
infixr 3 ·⇛·
infixl 3 ·⇐·
infixl 3 ·⇚·
infix  2  ⊢

(⊗), (⇒), (⇐), (⊕), (⇚), (⇛) :: (IsFormula n x, IsFormula n y) => x -> y -> Formula n
x ⊗ y = Op Prod [toFormula x, toFormula y]
x ⇒ y = Op ImpR [toFormula x, toFormula y]
x ⇐ y = Op ImpL [toFormula x, toFormula y]
x ⊕ y = Op Plus [toFormula x, toFormula y]
x ⇚ y = Op SubL [toFormula x, toFormula y]
x ⇛ y = Op SubR [toFormula x, toFormula y]

(·⊗·), (·⇒·), (·⇐·), (·⊕·), (·⇚·), (·⇛·) :: (IsStructure n x, IsStructure n y) => x -> y -> Structure n
x ·⊗· y = Op Prod [toStructure x, toStructure y]
x ·⇒· y = Op ImpR [toStructure x, toStructure y]
x ·⇐· y = Op ImpL [toStructure x, toStructure y]
x ·⊕· y = Op Plus [toStructure x, toStructure y]
x ·⇚· y = Op SubL [toStructure x, toStructure y]
x ·⇛· y = Op SubR [toStructure x, toStructure y]
