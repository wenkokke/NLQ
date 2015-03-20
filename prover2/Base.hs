{-# LANGUAGE GADTs, PolyKinds, DataKinds, KindSignatures, TypeOperators, FlexibleInstances, UndecidableInstances, MultiParamTypeClasses, OverlappingInstances, StandaloneDeriving #-}
module Base where


-- * Base data structures

data Operator {-n :: Nat-} where
  Prod :: Operator {-2-}
  ImpR :: Operator {-2-}
  ImpL :: Operator {-2-}
  Plus :: Operator {-2-}
  SubL :: Operator {-2-}
  SubR :: Operator {-2-}
  deriving (Eq)

data Formula :: * where
  FVar :: String   -> Formula
  FOp  :: Operator -> [Formula] -> Formula
  deriving (Eq)

data Structure :: * where
  SVar :: String   -> Structure
  SEl  :: Formula  -> Structure
  SOp  :: Operator -> [Structure] -> Structure
  deriving (Eq)

data Judgement where
  Struct :: Structure -> Structure -> Judgement
  FocusL :: Formula   -> Structure -> Judgement
  FocusR :: Structure -> Formula   -> Judgement
  deriving (Eq)


-- * Show functions for judgements

instance Show Formula where
  showsPrec _ (FVar x)          = shows x
  showsPrec p (FOp Prod [x, y]) = showParen (p > 6) (showsPrec 6 x . showString " ⊗ " . showsPrec 6 y)
  showsPrec p (FOp ImpR [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇒ " . showsPrec 5 y)
  showsPrec p (FOp ImpL [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇐ " . showsPrec 5 y)
  showsPrec p (FOp Plus [x, y]) = showParen (p > 6) (showsPrec 6 x . showString " ⊕ " . showsPrec 6 y)
  showsPrec p (FOp SubL [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇚ " . showsPrec 5 y)
  showsPrec p (FOp SubR [x, y]) = showParen (p > 5) (showsPrec 5 x . showString " ⇛ " . showsPrec 5 y)

instance Show Structure where
  showsPrec _ (SVar x)          = shows x
  showsPrec _ (SEl x)           = shows x
  showsPrec p (SOp Prod [x, y]) = showParen (p > 4) (showsPrec 4 x . showString " ⊗ " . showsPrec 4 y)
  showsPrec p (SOp ImpR [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ⇒ " . showsPrec 3 y)
  showsPrec p (SOp ImpL [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ⇐ " . showsPrec 3 y)
  showsPrec p (SOp Plus [x, y]) = showParen (p > 4) (showsPrec 4 x . showString " ⊕ " . showsPrec 4 y)
  showsPrec p (SOp SubL [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ⇚ " . showsPrec 3 y)
  showsPrec p (SOp SubR [x, y]) = showParen (p > 3) (showsPrec 3 x . showString " ⇛ " . showsPrec 3 y)

instance Show Judgement where
  showsPrec _ (Struct x y) =                   shows x . showString   " ⊢ "   . shows y
  showsPrec _ (FocusL x y) = showString "[ " . shows x . showString " ] ⊢ "   . shows y
  showsPrec _ (FocusR x y) =                   shows x . showString   " ⊢ [ " . shows y . showString " ]"


-- * Conversions to `Formula`, `Structure` and `Judgement`

isFormula :: String -> Bool
isFormula x = x `elem` ["A","B","C","D"]

isStructure :: String -> Bool
isStructure x = x `elem` ["X","Y","Z","W"]

class IsFormula   a where toFormula   :: a -> Formula
class IsStructure a where toStructure :: a -> Structure
class IsJudgement (x :: *) (y :: *) where (⊢) :: x -> y -> Judgement

instance IsFormula   Formula   where toFormula   = id
instance IsFormula   String    where toFormula   = FVar
instance IsStructure Structure where toStructure = id
instance IsStructure Formula   where toStructure = SEl
instance IsStructure String    where toStructure x
                                       | isFormula   x = SEl (FVar x)
                                       | isStructure x = SVar x

instance IsJudgement Structure Structure  where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement Formula   Formula    where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement String    String     where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement Structure Formula    where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement Formula   Structure  where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement Structure String     where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement String    Structure  where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement Formula   String     where x ⊢ y = Struct (toStructure x) (toStructure y)
instance IsJudgement String    Formula    where x ⊢ y = Struct (toStructure x) (toStructure y)

instance IsJudgement [Formula] Structure where x ⊢ y = FocusL (toFormula (head x)) (toStructure y)
instance IsJudgement Structure [Formula] where x ⊢ y = FocusR (toStructure x) (toFormula (head y))
instance IsJudgement [Formula] Formula   where x ⊢ y = FocusL (toFormula (head x)) (toStructure y)
instance IsJudgement Formula   [Formula] where x ⊢ y = FocusR (toStructure x) (toFormula (head y))
instance IsJudgement [Formula] String    where x ⊢ y = FocusL (toFormula (head x)) (toStructure y)
instance IsJudgement String    [Formula] where x ⊢ y = FocusR (toStructure x) (toFormula (head y))

instance IsJudgement [String]  Structure where x ⊢ y = FocusL (toFormula (head x)) (toStructure y)
instance IsJudgement Structure [String]  where x ⊢ y = FocusR (toStructure x) (toFormula (head y))
instance IsJudgement [String]  Formula   where x ⊢ y = FocusL (toFormula (head x)) (toStructure y)
instance IsJudgement Formula   [String]  where x ⊢ y = FocusR (toStructure x) (toFormula (head y))
instance IsJudgement [String]  String    where x ⊢ y = FocusL (toFormula (head x)) (toStructure y)
instance IsJudgement String    [String]  where x ⊢ y = FocusR (toStructure x) (toFormula (head y))


-- * Syntactic sugar for writing `Formula`, `Structure` and `Judgement`

infixr 6 ⊗
infixr 6 ⊕
infixr 5 ⇒
infixr 5 ⇛
infixl 5 ⇐
infixl 5 ⇚
infixr 4 ·⊗·
infixr 4 ·⊕·
infixr 3 ·⇒·
infixr 3 ·⇛·
infixl 3 ·⇐·
infixl 3 ·⇚·
infix 2 ⊢

(⊗), (⇒), (⇐), (⊕), (⇚), (⇛) :: (IsFormula x, IsFormula y) => x -> y -> Formula
x ⊗ y = FOp Prod [toFormula x, toFormula y]
x ⇒ y = FOp ImpR [toFormula x, toFormula y]
x ⇐ y = FOp ImpL [toFormula x, toFormula y]
x ⊕ y = FOp Plus [toFormula x, toFormula y]
x ⇚ y = FOp SubL [toFormula x, toFormula y]
x ⇛ y = FOp SubR [toFormula x, toFormula y]

(·⊗·), (·⇒·), (·⇐·), (·⊕·), (·⇚·), (·⇛·) :: (IsStructure x, IsStructure y) => x -> y -> Structure
x ·⊗· y = SOp Prod [toStructure x, toStructure y]
x ·⇒· y = SOp ImpR [toStructure x, toStructure y]
x ·⇐· y = SOp ImpL [toStructure x, toStructure y]
x ·⊕· y = SOp Plus [toStructure x, toStructure y]
x ·⇚· y = SOp SubL [toStructure x, toStructure y]
x ·⇛· y = SOp SubR [toStructure x, toStructure y]
