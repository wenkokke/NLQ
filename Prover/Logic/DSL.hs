{-# LANGUAGE FunctionalDependencies, FlexibleInstances, TypeSynonymInstances #-}
module Logic.DSL where


import Prover hiding (Term)
import Logic.Base
import Logic.Printing ()


infixr 7  ⊗
infixl 7  ⊕
infixr 6  ⇒
infixl 6  ⇐
infixl 6  ⇚
infixr 6  ⇛
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
    | otherwise   = error ("invalid formula '"++show t++"'")

instance IsFormula VarId VarId where
  asFormula n
    | n `elem` ["A","B","C","D"] = Var n
    | otherwise                  = Con (Atom n) []

instance (Show v) => IsStructure (Term v) v where
  asStructure t
    | isStructure t = t
    | isFormula   t = Con Down [asFormula t]
    | otherwise     = error ("invalid structure '"++show t++"'")

instance IsStructure VarId VarId where
  asStructure n
    | n `elem` ["X","Y","Z","W"] = Var n
    | otherwise                  = Con Down [asFormula n]


instance (Show v) => IsJudgement (Term v) (Term v) v where x ⊢ y = sbin JStruct x y
instance IsJudgement       VarId (Term VarId) VarId  where x ⊢ y = sbin JStruct x y
instance IsJudgement (Term VarId)      VarId  VarId  where x ⊢ y = sbin JStruct x y
instance IsJudgement       VarId       VarId  VarId  where x ⊢ y = sbin JStruct x y


instance (Show v) => IsJudgement [Term v] (Term v) v where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]
instance IsJudgement [VarId] (Term VarId) VarId where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]
instance IsJudgement [Term VarId] (VarId) VarId where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]
instance IsJudgement [VarId] (VarId) VarId where
  [a] ⊢ y = Con JFocusL [asFormula a, asStructure y]


instance (Show v) => IsJudgement (Term v) [Term v] v where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]
instance IsJudgement (VarId) [Term VarId] VarId where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]
instance IsJudgement (Term VarId) [VarId] VarId where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]
instance IsJudgement (VarId) [VarId] VarId where
  x ⊢ [b] = Con JFocusR [asStructure x, asFormula b]


(⊗), (⇒), (⇐), (⊕), (⇚), (⇛) :: (IsFormula t1 v, IsFormula t2 v) => t1 -> t2 -> Term v
(⊗) = fbin FProd
(⇒) = fbin FImpR
(⇐) = fbin FImpL
(⊕) = fbin FPlus
(⇚) = fbin FSubL
(⇛) = fbin FSubR

(·⊗·), (·⇒·), (·⇐·), (·⊕·), (·⇚·), (·⇛·) :: (IsStructure t1 v, IsStructure t2 v) => t1 -> t2 -> Term v
(·⊗·) = sbin SProd
(·⇒·) = sbin SImpR
(·⇐·) = sbin SImpL
(·⊕·) = sbin SPlus
(·⇚·) = sbin SSubL
(·⇛·) = sbin SSubR
