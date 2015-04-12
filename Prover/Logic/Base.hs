{-# LANGUAGE DeriveGeneric #-}
module Logic.Base where


import           Control.DeepSeq
import           Data.Hashable
import           Data.Void (Void)
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
  | FProd   | FImpR   | FImpL
  | FPlus   | FSubL   | FSubR

  -- structural operators
  | SProd   | SImpR   | SImpL
  | SPlus   | SSubL   | SSubR

  -- sequents
  | JStruct | JFocusL | JFocusR

  deriving (Eq,Ord,Generic)


instance Hashable ConId
instance NFData   ConId


type VarId  = String
type Term v = Prover.Term ConId v
type RuleId = String
type Proof  = Prover.Term RuleId Void


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
pos _                = False

neg (Con (Atom n) _) = isNegativeAtom n
neg (Con  FPlus   _) = True
neg (Con  FImpR   _) = True
neg (Con  FImpL   _) = True
neg _                = False