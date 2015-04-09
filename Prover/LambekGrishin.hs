{-# LANGUAGE FunctionalDependencies, FlexibleInstances, TypeSynonymInstances #-}
module Main where


import           Data.Data (Fixity (..))
import           Data.Void (Void)
import           Prover hiding (Term)
import qualified Prover (Term)
import           Text.Printf (printf)


-- * Terms, Variables, Constructors

data ConId

  = Atom String
  | Down

  | FProd   | FImpR   | FImpL
  | FPlus   | FSubL   | FSubR

  | SProd   | SImpR   | SImpL
  | SPlus   | SSubL   | SSubR

  | JStruct | JFocusL | JFocusR
  deriving (Eq,Ord)

type Term v = Prover.Term ConId v


-- * Well-Formed Terms

isFormula :: Term v -> Bool
isFormula (Var          _) = True
isFormula (Con (Atom _) _) = True
isFormula (Con FProd args) = all isFormula args
isFormula (Con FImpR args) = all isFormula args
isFormula (Con FImpL args) = all isFormula args
isFormula (Con FPlus args) = all isFormula args
isFormula (Con FSubL args) = all isFormula args
isFormula (Con FSubR args) = all isFormula args
isFormula (Con _     _   ) = False

isStructure :: Term v -> Bool
isStructure (Var          _) = True
isStructure (Con SProd args) = all isStructure args
isStructure (Con SImpR args) = all isStructure args
isStructure (Con SImpL args) = all isStructure args
isStructure (Con SPlus args) = all isStructure args
isStructure (Con SSubL args) = all isStructure args
isStructure (Con SSubR args) = all isStructure args
isStructure (Con Down  [fm]) = isFormula fm
isStructure (Con _     _   ) = False

isJudgement :: Term v -> Bool
isJudgement (Con JStruct [x,y]) = isStructure x && isStructure y
isJudgement (Con JFocusL [a,y]) = isFormula   a && isStructure y
isJudgement (Con JFocusR [x,b]) = isStructure x && isFormula   b
isJudgement _                   = False



-- * Syntactic Sugar


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

class IsFormula   t     v | t     -> v where asFormula   :: t -> Term v
class IsStructure t     v | t     -> v where asStructure :: t -> Term v
class IsJudgement t1 t2 v | t1 t2 -> v where (⊢)  :: t1 -> t2 -> Term v

instance (Show v) => IsFormula (Term v) v where
  asFormula t | isFormula t = t
  asFormula t = error ("Invalid formula: "++show t)

instance IsFormula VarId VarId where
  asFormula n | n `elem` ["A","B","C","D"] = Var n

instance (Show v) => IsStructure (Term v) v where
  asStructure t | isStructure t = t
  asStructure t = Con Down [asFormula t]

instance IsStructure VarId VarId where
  asStructure n | n `elem` ["X","Y","Z","W"] = Var n
  asStructure n = Con Down [asFormula n]

instance (Show v) => IsJudgement (Term v) (Term v) v where
  x ⊢ y = Con JStruct [asStructure x, asStructure y]
instance IsJudgement VarId (Term VarId) VarId where
  x ⊢ y = Con JStruct [asStructure x, asStructure y]
instance IsJudgement (Term VarId) VarId VarId where
  x ⊢ y = Con JStruct [asStructure x, asStructure y]
instance IsJudgement VarId VarId VarId where
  x ⊢ y = Con JStruct [asStructure x, asStructure y]

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
x ⊗ y = Con FProd [asFormula x, asFormula y]
x ⇒ y = Con FImpR [asFormula x, asFormula y]
x ⇐ y = Con FImpL [asFormula x, asFormula y]
x ⊕ y = Con FPlus [asFormula x, asFormula y]
x ⇚ y = Con FSubL [asFormula x, asFormula y]
x ⇛ y = Con FSubR [asFormula x, asFormula y]


(·⊗·), (·⇒·), (·⇐·), (·⊕·), (·⇚·), (·⇛·) :: (IsStructure t1 v, IsStructure t2 v) => t1 -> t2 -> Term v
x ·⊗· y = Con SProd [asStructure x, asStructure y]
x ·⇒· y = Con SImpR [asStructure x, asStructure y]
x ·⇐· y = Con SImpL [asStructure x, asStructure y]
x ·⊕· y = Con SPlus [asStructure x, asStructure y]
x ·⇚· y = Con SSubL [asStructure x, asStructure y]
x ·⇛· y = Con SSubR [asStructure x, asStructure y]


-- * Rule declarations

rules :: [Rule String ConId Int]
rules =
  [ ( [] ⟶   "A"   ⊢ [ "A" ] ) "ax⁻"
  , ( [] ⟶ [ "A" ] ⊢   "A"   ) "ax⁺"

    -- focusing
  , ( [   "X"   ⊢   "B"   ] ⟶   "X"   ⊢ [ "B" ] ) "⇁"
  , ( [   "A"   ⊢   "Y"   ] ⟶ [ "A" ] ⊢   "Y"   ) "↽"
  , ( [   "X"   ⊢ [ "B" ] ] ⟶   "X"   ⊢   "B"   ) "⇀"
  , ( [ [ "A" ] ⊢   "Y"   ] ⟶   "A"   ⊢   "Y"   ) "↼"

    -- rules for (⇐ , ⊗ , ⇒)
  , ( [ "A" ·⊗· "B" ⊢ "Y" ]             ⟶ "A" ⊗ "B" ⊢ "Y"             ) "⊗ᴸ"
  , ( [ "X" ⊢ [ "A" ] , "Y" ⊢ [ "B" ] ] ⟶ "X" ·⊗· "Y" ⊢ [ "A" ⊗ "B" ] ) "⊗ᴿ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ [ "A" ⇒ "B" ] ⊢ "X" ·⇒· "Y" ) "⇒ᴸ"
  , ( [ "X" ⊢ "A" ·⇒· "B" ]             ⟶ "X" ⊢ "A" ⇒ "B"             ) "⇒ᴿ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ [ "B" ⇐ "A" ] ⊢ "Y" ·⇐· "X" ) "⇐ᴸ"
  , ( [ "X" ⊢ "B" ·⇐· "A" ]             ⟶ "X" ⊢ "B" ⇐ "A"             ) "⇐ᴿ"

  , ( [ "Y" ⊢ "X" ·⇒· "Z" ]             ⟶ "X" ·⊗· "Y" ⊢ "Z"           ) "r⇒⊗"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ]             ⟶ "Y" ⊢ "X" ·⇒· "Z"           ) "r⊗⇒"
  , ( [ "X" ⊢ "Z" ·⇐· "Y" ]             ⟶ "X" ·⊗· "Y" ⊢ "Z"           ) "r⇐⊗"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ]             ⟶ "X" ⊢ "Z" ·⇐· "Y"           ) "r⊗⇐"

    -- rules for (⇚ , ⊕ , ⇛)
  , ( [ [ "B" ] ⊢ "Y" , [ "A" ] ⊢ "X" ] ⟶ [ "B" ⊕ "A" ] ⊢ "Y" ⊕ "X"   ) "⊕ᴸ"
  , ( [ "X" ⊢ "B" ·⊕· "A" ]             ⟶ "X" ⊢ "B" ⊕ "A"             ) "⊕ᴿ"
  , ( [ "A" ·⇚· "B" ⊢ "X" ]             ⟶ "A" ⇚ "B" ⊢ "X"             ) "⇚ᴸ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ "X" ·⇚· "Y" ⊢ [ "A" ⇚ "B" ] ) "⇚ᴿ"
  , ( [ "B" ·⇛· "A" ⊢ "X" ]             ⟶ "B" ⇛ "A" ⊢ "X"             ) "⇛ᴸ"
  , ( [ "X" ⊢ [ "A" ] , [ "B" ] ⊢ "Y" ] ⟶ "Y" ·⇛· "X" ⊢ [ "B" ⇛ "A" ] ) "⇛ᴿ"

  , ( [ "Z" ·⇚· "X" ⊢ "Y" ]             ⟶ "Z" ⊢ "Y" ·⊕· "X"           ) "r⇚⊕"
  , ( [ "Z" ⊢ "Y" ·⊕· "X" ]             ⟶ "Z" ·⇚· "X" ⊢ "Y"           ) "r⊕⇚"
  , ( [ "Y" ·⇛· "Z" ⊢ "X" ]             ⟶ "Z" ⊢ "Y" ·⊕· "X"           ) "r⇛⊕"
  , ( [ "Z" ⊢ "Y" ·⊕· "X" ]             ⟶ "Y" ·⇛· "Z" ⊢ "X"           ) "r⊕⇛"

    -- grishin interaction principles
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "X" ⊢ "W" ·⇐· "Y"   ) "d⇛⇐"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Z" ·⇛· "Y" ⊢ "X" ·⇒· "W"   ) "d⇛⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "Y" ·⇚· "W" ⊢ "X" ·⇒· "Z"   ) "d⇚⇒"
  , ( [ "X" ·⊗· "Y" ⊢ "Z" ·⊕· "W" ]     ⟶ "X" ·⇚· "W" ⊢ "Z" ·⇐· "Y"   ) "d⇚⇐"
  ]


-- * An example

s, n, np :: Term Void
s  = Con (Atom "S" ) []
n  = Con (Atom "N" ) []
np = Con (Atom "NP") []


mary, thinks, someone, left :: Term Void
mary    =  np
thinks  = (np ⇒ s) ⇐ s
someone = (np ⇐ n) ⊗ n
left    =  np ⇒ s


goal :: Term Void
goal = mary ·⊗· thinks ·⊗· someone ·⊗· left ⊢ s


main :: IO ()
main = print (search goal rules)


-- * Parsing formulas

-- * Printing formulas

instance Show ConId where

  show (Atom x) = x
  show  FProd   = "⊗"
  show  FImpR   = "⇒"
  show  FImpL   = "⇐"
  show  FPlus   = "⊕"
  show  FSubL   = "⇚"
  show  FSubR   = "⇛"
  show  Down    = ""
  show  SProd   = "·⊗·"
  show  SImpR   = "·⇒·"
  show  SImpL   = "·⇐·"
  show  SPlus   = "·⊕·"
  show  SSubL   = "·⇚·"
  show  SSubR   = "·⇛·"
  show  JStruct = "⊢"
  show  JFocusL = "⊢"
  show  JFocusR = "⊢"

instance Prec ConId where

  prec (Atom _) = 9
  prec  FProd   = 8
  prec  FImpR   = 7
  prec  FImpL   = 7
  prec  FPlus   = 8
  prec  FSubL   = 7
  prec  FSubR   = 7
  prec  Down    = 6
  prec  SProd   = 5
  prec  SImpR   = 4
  prec  SImpL   = 4
  prec  SPlus   = 5
  prec  SSubL   = 4
  prec  SSubR   = 4
  prec  JStruct = 3
  prec  JFocusL = 3
  prec  JFocusR = 3

  fixity (Atom _) = Prefix
  fixity  FProd   = Infix
  fixity  FImpR   = Infix
  fixity  FImpL   = Infix
  fixity  FPlus   = Infix
  fixity  FSubL   = Infix
  fixity  FSubR   = Infix
  fixity  Down    = Prefix
  fixity  SProd   = Infix
  fixity  SImpR   = Infix
  fixity  SImpL   = Infix
  fixity  SPlus   = Infix
  fixity  SSubL   = Infix
  fixity  SSubR   = Infix
  fixity  JStruct = Infix
  fixity  JFocusL = Infix
  fixity  JFocusR = Infix
