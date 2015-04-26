{-# LANGUAGE DeriveGeneric, TypeSynonymInstances, FlexibleInstances #-}
module Logic.Base (Term,ConId(..),Proof,nullary,unary,binary,IsVar(..),pos,neg,posAtom,negAtom,module X) where


import           Control.DeepSeq (NFData)
import           Data.Hashable (Hashable)
import           Data.Void (Void,absurd)
import           GHC.Generics (Generic)

import           Logic.Prover as X hiding (Term)
import qualified Logic.Prover as Prover (Term)


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

posAtom :: String -> Bool
posAtom n = not (negAtom n)

negAtom :: String -> Bool
negAtom n = let c = last n in c == '⁻' || c == '\''

pos,neg :: Term v -> Bool
pos (Var          _) = True
pos (Con (Atom n) _) = posAtom n
pos (Con  FProd   _) = True
pos (Con  FSubL   _) = True
pos (Con  FSubR   _) = True
pos (Con  HProd   _) = True
pos (Con  F1L     _) = True
pos (Con  F1R     _) = True
pos (Con  FDia    _) = True
pos _                = False

neg (Con (Atom n) _) = negAtom n
neg (Var          _) = True
neg (Con  FPlus   _) = True
neg (Con  FImpR   _) = True
neg (Con  FImpL   _) = True
neg (Con  HImpR   _) = True
neg (Con  HImpL   _) = True
neg (Con  F0L     _) = True
neg (Con  F0R     _) = True
neg (Con  FBox    _) = True
neg _                = False
