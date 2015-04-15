{-# LANGUAGE DeriveGeneric, TypeSynonymInstances, FlexibleInstances #-}
module Logic.Base where


import           Control.DeepSeq
import           Data.Hashable
import           Data.Void (Void,absurd)
import           GHC.Generics

import           Prover hiding (Term)
import qualified Prover (Term)


-- * Terms, Variables, Constructors

data ConId

  -- atomic formulas
  = Atom String

  -- mediator between logical and structural formulas
  | Down

  -- logical operators
  | FProd | FImpR | FImpL
  | FPlus | FSubL | FSubR
  | F0L   | F0R   | FBox
  | F1L   | F1R   | FDia

  -- structural operators
  | SProd | SImpR | SImpL
  | SPlus | SSubL | SSubR
  | S0L   | S0R   | SBox
  | S1L   | S1R   | SDia

  -- hollow product and slashes
  | HProd | HImpR | HImpL

  -- sequents
  | JForm   | JStruct
  | JFocusL | JFocusR

  deriving (Eq,Ord,Show,Generic)


instance (Show v) => Show (Term v) where
  showsPrec _ (Var i)    = shows i
  showsPrec _ (Con f []) = shows f
  showsPrec p (Con f xs) =
    showParen (p >= 1) $ shows f . showSeq (showsPrec 1) xs
    where
      showSeq _  []     = id
      showSeq ss (x:xs) = showChar ' ' . ss x . showSeq ss xs


instance Hashable ConId
instance NFData   ConId


type Term v = Prover.Term ConId v
type RuleId = String
type Proof  = Prover.Term RuleId Void


-- * Utility constructors

nullary :: ConId -> Term v
nullary c = Con c []

unary   :: ConId -> Term v -> Term v
unary   c x = Con c [x]

binary  :: ConId -> Term v -> Term v -> Term v
binary  c x y = Con c [x,y]


-- * Well-Formed Terms

class IsVar v where
  forFormula   :: v -> Bool
  forStructure :: v -> Bool

instance IsVar Void where
  forFormula   = absurd
  forStructure = absurd

instance IsVar String where
  forFormula   n = n `elem` ["A","B","C","D"]
  forStructure n = n `elem` ["X","Y","Z","W"]


isFormula :: (IsVar v) => Term v -> Bool
isFormula (Var          n) = forFormula n
isFormula (Con (Atom  _) _) = True
isFormula (Con  FProd args) = all isFormula args
isFormula (Con  FImpR args) = all isFormula args
isFormula (Con  FImpL args) = all isFormula args
isFormula (Con  FPlus args) = all isFormula args
isFormula (Con  FSubL args) = all isFormula args
isFormula (Con  FSubR args) = all isFormula args
isFormula (Con  HProd args) = all isFormula args
isFormula (Con  HImpR args) = all isFormula args
isFormula (Con  HImpL args) = all isFormula args
isFormula (Con  F0L   args) = all isFormula args
isFormula (Con  F0R   args) = all isFormula args
isFormula (Con  FBox  args) = all isFormula args
isFormula (Con  F1L   args) = all isFormula args
isFormula (Con  F1R   args) = all isFormula args
isFormula (Con  FDia  args) = all isFormula args
isFormula (Con  _     _   ) = False

isStructure :: (IsVar v) => Term v -> Bool
isStructure (Var           n) = forStructure n
isStructure (Con  SProd args) = all isStructure args
isStructure (Con  SImpR args) = all isStructure args
isStructure (Con  SImpL args) = all isStructure args
isStructure (Con  SPlus args) = all isStructure args
isStructure (Con  SSubL args) = all isStructure args
isStructure (Con  SSubR args) = all isStructure args
isStructure (Con  S0L   args) = all isStructure args
isStructure (Con  S0R   args) = all isStructure args
isStructure (Con  SBox  args) = all isStructure args
isStructure (Con  S1L   args) = all isStructure args
isStructure (Con  S1R   args) = all isStructure args
isStructure (Con  SDia  args) = all isStructure args
isStructure (Con  Down  [fm]) = isFormula fm
isStructure (Con  _     _   ) = False

isJudgement :: (IsVar v) => Term v -> Bool
isJudgement (Con JForm   [a,b]) = isFormula   a && isFormula   b
isJudgement (Con JStruct [x,y]) = isStructure x && isStructure y
isJudgement (Con JFocusL [a,y]) = isFormula   a && isStructure y
isJudgement (Con JFocusR [x,b]) = isStructure x && isFormula   b
isJudgement _                   = False


-- * Polarities

isAtom :: Term Void -> Bool
isAtom (Con (Atom _) _) = True
isAtom _                = False

isPositiveAtom :: String -> Bool
isPositiveAtom n = not (isNegativeAtom n)

isNegativeAtom :: String -> Bool
isNegativeAtom n = let c = last n in c == '⁻' || c == '\''

pos,neg :: Term Void -> Bool
pos (Con (Atom n) _) = isPositiveAtom n
pos (Con  FProd   _) = True
pos (Con  FSubL   _) = True
pos (Con  FSubR   _) = True
pos (Con  HProd   _) = True
pos (Con  F1L     _) = True
pos (Con  F1R     _) = True
pos (Con  FDia    _) = True
pos _                = False

neg (Con (Atom n) _) = isNegativeAtom n
neg (Con  FPlus   _) = True
neg (Con  FImpR   _) = True
neg (Con  FImpL   _) = True
neg (Con  HImpR   _) = True
neg (Con  HImpL   _) = True
neg (Con  F0L     _) = True
neg (Con  F0R     _) = True
neg (Con  FBox    _) = True
neg _                = False
