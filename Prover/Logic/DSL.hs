{-# LANGUAGE FunctionalDependencies, FlexibleInstances, TypeSynonymInstances #-}
module Logic.DSL where


import Prover hiding (Term)
import Logic.Base
import Logic.Printing (Agda(..))


infixr 9  ◇
infixr 9  □
infixr 8  ⊗
infixl 8  ⊕
infixr 7  ⇒
infixl 7  ⇐
infixl 7  ⇚
infixr 7  ⇛
infixr 6  ◇·
infixr 6  □·
infixr 5 ·⊗·
infixl 5 ·⊕·
infixr 4 ·⇒·
infixl 4 ·⇐·
infixl 4 ·⇚·
infixr 4 ·⇛·
infix  3  ⊢

down :: (IsFormula t v) => t -> Term v
down x = Con Down [asFormula x]

fbin :: (IsFormula t1 v, IsFormula t2 v) => ConId -> t1 -> t2 -> Term v
fbin f x y = Con f [asFormula x, asFormula y]

sbin :: (IsStructure t1 v, IsStructure t2 v) => ConId -> t1 -> t2 -> Term v
sbin f x y = Con f [asStructure x, asStructure y]


class IsFormula   t     v | t     -> v where asFormula   :: t -> Term v
class IsStructure t     v | t     -> v where asStructure :: t -> Term v
class IsJudgement t1 t2 v | t1 t2 -> v where (⊢)  :: t1 -> t2 -> Term v


instance (Show v) => IsFormula (Term v) v where
  asFormula t
    | isFormula t = t
    | otherwise   = error ("invalid formula '"++show (Agda t)++"'")

instance IsFormula String String where
  asFormula n
    | n `elem` ["A","B","C","D"] = Var n
    | otherwise                  = Con (Atom n) []

instance (Show v) => IsStructure (Term v) v where
  asStructure t
    | isStructure t = t
    | isFormula   t = Con Down [asFormula t]
    | otherwise     = error ("invalid structure '"++show (Agda t)++"'")

instance IsStructure String String where
  asStructure n
    | n `elem` ["X","Y","Z","W"] = Var n
    | otherwise                  = Con Down [asFormula n]


instance (Show v) => IsJudgement (Term v) (Term v) v where x ⊢ y = sbin JStruct x y
instance IsJudgement       String (Term String) String  where x ⊢ y = sbin JStruct x y
instance IsJudgement (Term String)      String  String  where x ⊢ y = sbin JStruct x y
instance IsJudgement       String       String  String  where x ⊢ y = sbin JStruct x y


instance (Show v) => IsJudgement [Term v] (Term v) v where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]
instance IsJudgement [String] (Term String) String where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]
instance IsJudgement [Term String] (String) String where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]
instance IsJudgement [String] (String) String where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]


instance (Show v) => IsJudgement (Term v) [Term v] v where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]
instance IsJudgement (String) [Term String] String where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]
instance IsJudgement (Term String) [String] String where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]
instance IsJudgement (String) [String] String where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]


(◇), (□) :: IsFormula t v => t -> Term v
(◇) x = Con FDia [asFormula x]
(□) x = Con FBox [asFormula x]

(⊗), (⇒), (⇐) :: (IsFormula t1 v, IsFormula t2 v) => t1 -> t2 -> Term v
(⊗) = fbin FProd
(⇒) = fbin FImpR
(⇐) = fbin FImpL
(⊕), (⇚), (⇛) :: (IsFormula t1 v, IsFormula t2 v) => t1 -> t2 -> Term v
(⊕) = fbin FPlus
(⇚) = fbin FSubL
(⇛) = fbin FSubR

(◇·), (□·) :: IsStructure t v => t -> Term v
(◇·) x = Con SDia [asStructure x]
(□·) x = Con SBox [asStructure x]

(·⊗·), (·⇒·), (·⇐·) :: (IsStructure t1 v, IsStructure t2 v) => t1 -> t2 -> Term v
(·⊗·) = sbin SProd
(·⇒·) = sbin SImpR
(·⇐·) = sbin SImpL
(·⊕·), (·⇚·), (·⇛·) :: (IsStructure t1 v, IsStructure t2 v) => t1 -> t2 -> Term v
(·⊕·) = sbin SPlus
(·⇚·) = sbin SSubL
(·⇛·) = sbin SSubR
