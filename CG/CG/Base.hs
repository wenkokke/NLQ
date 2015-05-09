{-# LANGUAGE DeriveGeneric, TypeSynonymInstances, FlexibleInstances #-}
module CG.Base (Term,ConId(..),Proof,nullary,unary,binary,IsVar(..)
               ,isPositive,isNegative,isAtomic,isPositiveAtom,isNegativeAtom
               ,module X) where


import           Control.DeepSeq (NFData)
import           Data.Hashable (Hashable)
import           Data.Void (Void,absurd)
import           GHC.Generics (Generic)

import           CG.Prover as X hiding (Term)
import qualified CG.Prover as Prover (Term)


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
  | Comma

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


-- * Polarities

isPositiveAtom :: String -> Bool
isPositiveAtom n = not (isNegativeAtom n)

isNegativeAtom :: String -> Bool
isNegativeAtom n = let c = last n in c == '⁻' || c == '\''

isAtomic :: Term v -> Bool
isAtomic (Con (Atom _) _) = True
isAtomic _                = False

isPositive,isNegative :: Term v -> Bool
isPositive (Var          _) = True
isPositive (Con (Atom n) _) = isPositiveAtom n
isPositive (Con  FProd   _) = True
isPositive (Con  FSubL   _) = True
isPositive (Con  FSubR   _) = True
isPositive (Con  HProd   _) = True
isPositive (Con  F1L     _) = True
isPositive (Con  F1R     _) = True
isPositive (Con  FDia    _) = True
isPositive _                = False

isNegative (Con (Atom n) _) = isNegativeAtom n
isNegative (Var          _) = True
isNegative (Con  FPlus   _) = True
isNegative (Con  FImpR   _) = True
isNegative (Con  FImpL   _) = True
isNegative (Con  HImpR   _) = True
isNegative (Con  HImpL   _) = True
isNegative (Con  F0L     _) = True
isNegative (Con  F0R     _) = True
isNegative (Con  FBox    _) = True
isNegative _                = False
