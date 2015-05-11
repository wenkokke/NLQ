{-# LANGUAGE DeriveGeneric, TypeSynonymInstances, FlexibleInstances,
    FlexibleContexts, RecordWildCards, UndecidableInstances #-}
module CG.Base (ConId(..)
               ,nullary,unary,binary
               ,unaryLogical,unaryStructural
               ,binaryLogical,binaryStructural
               ,sequents
               ,toLogical,toStructural
               ,ASCII(..),Result(..)
               ,module X
               ) where


import CG.Prover as X
import Control.DeepSeq (NFData)
import Data.Hashable   (Hashable)
import Data.Serialize  (Serialize)
import Data.Void       (Void)
import GHC.Generics    (Generic)


-- * Operators

data ConId

  -- atomic formulas
  = PosAtom String
  | NegAtom String

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
  | JAlgebr | JStruct
  | JFocusL | JFocusR

  deriving (Eq,Ord,Generic)


instance Hashable  ConId
instance NFData    ConId
instance Serialize ConId


-- * Groupings of operators.

unaryLogical :: [ConId]
unaryLogical = [F0L, F0R, FBox, F1L, F1R, FDia, HProd, HImpR, HImpL]

unaryStructural :: [ConId]
unaryStructural = [S0L, S0R, SBox, S1L, S1R, SDia]

binaryLogical :: [ConId]
binaryLogical = [FProd, FImpR, FImpL, FPlus, FSubL, FSubR]

binaryStructural :: [ConId]
binaryStructural = [SProd, SImpR, SImpL, SPlus, SSubL, SSubR, Comma]

sequents :: [ConId]
sequents = [JAlgebr, JStruct, JFocusL, JFocusL]


-- |Convert structural operators to their logical equivalents.
toLogical :: ConId -> ConId
toLogical SProd = FProd
toLogical SImpR = FImpR
toLogical SImpL = FImpL
toLogical SPlus = FPlus
toLogical SSubL = FSubL
toLogical SSubR = FSubR
toLogical S0L   = F0L
toLogical S0R   = F0R
toLogical SBox  = FBox
toLogical S1L   = F1L
toLogical S1R   = F1R
toLogical SDia  = FDia
toLogical c     = c


-- |Convert logical operators to their structural equivalents.
toStructural :: ConId -> ConId
toStructural FProd = SProd
toStructural FImpR = SImpR
toStructural FImpL = SImpL
toStructural FPlus = SPlus
toStructural FSubL = SSubL
toStructural FSubR = SSubR
toStructural F0L   = S0L
toStructural F0R   = S0R
toStructural FBox  = SBox
toStructural F1L   = S1L
toStructural F1R   = S1R
toStructural FDia  = SDia
toStructural c     = c


-- * Utility constructors

nullary :: ConId -> Term ConId v
nullary c = Con c []

unary   :: ConId -> Term ConId v -> Term ConId v
unary   c x = Con c [x]

binary  :: ConId -> Term ConId v -> Term ConId v -> Term ConId v
binary  c x y = Con c [x,y]


-- * Guards

instance Guardable ConId where

  isAtomic (Con (PosAtom _) _) = True
  isAtomic (Con (NegAtom _) _) = True
  isAtomic _                   = False

  isPositive (Var          _)    = True
  isPositive (Con (PosAtom _) _) = True
  isPositive (Con (NegAtom _) _) = False
  isPositive (Con  FProd   _)    = True
  isPositive (Con  FSubL   _)    = True
  isPositive (Con  FSubR   _)    = True
  isPositive (Con  HProd   _)    = True
  isPositive (Con  F1L     _)    = True
  isPositive (Con  F1R     _)    = True
  isPositive (Con  FDia    _)    = True
  isPositive _                   = False

  isNegative (Var          _)    = True
  isNegative (Con (PosAtom _) _) = False
  isNegative (Con (NegAtom _) _) = True
  isNegative (Con  FPlus   _)    = True
  isNegative (Con  FImpR   _)    = True
  isNegative (Con  FImpL   _)    = True
  isNegative (Con  HImpR   _)    = True
  isNegative (Con  HImpL   _)    = True
  isNegative (Con  F0L     _)    = True
  isNegative (Con  F0R     _)    = True
  isNegative (Con  FBox    _)    = True
  isNegative _                   = False



-- * Printing

instance Show ConId where
  show (PosAtom x) = x
  show (NegAtom x) = x ++ "⁻"
  show F0L     = "₀"; show F0R     = "⁰"; show FBox  = "□"
  show F1L     = "₁"; show F1R     = "¹"; show FDia  = "◇"
  show FProd   = "⊗"; show FImpR   = "⇒"; show FImpL = "⇐"
  show SProd   = "⊗"; show SImpR   = "⇒"; show SImpL = "⇐"
  show HProd   = "∘"; show HImpR   = "⇨"; show HImpL = "⇦"
  show FPlus   = "⊕"; show FSubL   = "⇚"; show FSubR = "⇛"
  show SPlus   = "⊕"; show SSubL   = "⇚"; show SSubR = "⇛"
  show S0L     = "₀"; show S0R     = "⁰"; show SBox  = "[]"
  show S1L     = "₁"; show S1R     = "¹"; show SDia  = "⟨⟩"
  show JAlgebr = "⊢"; show JStruct = "⊢"
  show JFocusL = "⊢"; show JFocusR = "⊢"
  show Down    = "·"; show Comma   = ","

instance Operator ConId where

  prec (PosAtom _) = 0
  prec (NegAtom _) = 0
  prec F0L     = 9; prec F0R     = 9; prec FBox  = 9
  prec F1L     = 9; prec F1R     = 9; prec FDia  = 9
  prec FProd   = 8; prec FImpR   = 7; prec FImpL = 7
  prec FPlus   = 8; prec FSubL   = 7; prec FSubR = 7
  prec HProd   = 8; prec HImpR   = 7; prec HImpL = 7
  prec S0L     = 6; prec S0R     = 6; prec SBox  = 0
  prec S1L     = 6; prec S1R     = 6; prec SDia  = 0
  prec SProd   = 5; prec SImpR   = 4; prec SImpL = 4
  prec SPlus   = 5; prec SSubL   = 4; prec SSubR = 4
  prec JAlgebr = 0; prec JStruct = 0
  prec JFocusL = 0; prec JFocusR = 0
  prec Down    = 0; prec Comma   = 3

  template (PosAtom x) _ = showString x . showChar ' '
  template (NegAtom x) _ = showString x . showString "⁻ "
  template F0L     [x]   = showString "₀ " . x
  template F0R     [x]   = x . showString "⁰ "
  template FBox    [x]   = showString "□ " . x
  template F1L     [x]   = showString "₁ " . x
  template F1R     [x]   = x . showString "¹ "
  template FDia    [x]   = showString "◇ " . x
  template FProd   [x,y] = x . showString "⊗ " . y
  template FImpR   [x,y] = x . showString "⇒ " . y
  template FImpL   [x,y] = x . showString "⇐ " . y
  template SProd   [x,y] = x . showString "⊗ " . y
  template SImpR   [x,y] = x . showString "⇒ " . y
  template SImpL   [x,y] = x . showString "⇐ " . y
  template HProd   [x,y] = x . showString "∘ " . y
  template HImpR   [x,y] = x . showString "⇨ " . y
  template HImpL   [x,y] = x . showString "⇦ " . y
  template FPlus   [x,y] = x . showString "⊕ " . y
  template FSubL   [x,y] = x . showString "⇚ " . y
  template FSubR   [x,y] = x . showString "⇛ " . y
  template SPlus   [x,y] = x . showString "⊕ " . y
  template SSubL   [x,y] = x . showString "⇚ " . y
  template SSubR   [x,y] = x . showString "⇛ " . y
  template S0L     [x]   = showString "₀ " . x
  template S0R     [x]   = x . showString "⁰ "
  template SBox    [x]   = showString "[ " . x . showString "]"
  template S1L     [x]   = showString "₁ " . x
  template S1R     [x]   = x . showString "¹ "
  template SDia    [x]   = showString "⟨ " . x . showString "⟩"
  template JAlgebr [x,y] = x . showString "⊢ " . y
  template JStruct [x,y] = x . showString "⊢ " . y
  template JFocusL [x,y] = showString "[ " . x . showString "]⊢ " . y
  template JFocusR [x,y] = x . showString "⊢[ " . y . showString "] "
  template Down    [x]   = showString "· " . x . showString "· "
  template Comma   [x,y] = x . showString ", " . y


-- * ASCII printing

newtype ASCII a = ASCII a

instance Show (ASCII ConId) where
  show (ASCII (PosAtom x)) = x
  show (ASCII (NegAtom x)) = x ++ "'"
  show (ASCII F0L)     = "0" ; show (ASCII F0R)     = "0" ; show (ASCII FBox)  = "[]"
  show (ASCII F1L)     = "1" ; show (ASCII F1R)     = "1" ; show (ASCII FDia)  = "<>"
  show (ASCII FProd)   = "*" ; show (ASCII FImpR)   = "->"; show (ASCII FImpL) = "<-"
  show (ASCII SProd)   = "*" ; show (ASCII SImpR)   = "->"; show (ASCII SImpL) = "<-"
  show (ASCII HProd)   = "o" ; show (ASCII HImpR)   = "-o"; show (ASCII HImpL) = "o-"
  show (ASCII FPlus)   = "+" ; show (ASCII FSubL)   = "<="; show (ASCII FSubR) = "=>"
  show (ASCII SPlus)   = "+" ; show (ASCII SSubL)   = "<="; show (ASCII SSubR) = "=>"
  show (ASCII S0L)     = "0" ; show (ASCII S0R)     = "0" ; show (ASCII SBox)  = "[]"
  show (ASCII S1L)     = "1" ; show (ASCII S1R)     = "1" ; show (ASCII SDia)  = "<>"
  show (ASCII JAlgebr) = "|-"; show (ASCII JStruct) = "|-"
  show (ASCII JFocusL) = "|-"; show (ASCII JFocusR) = "|-"
  show (ASCII Down)    = "." ; show (ASCII Comma)   = ","


-- * Proofs

type Proof = Term RuleId Void

data Result
  = Solved                 (Term ConId Void) Proof
  | Parsed String [String] (Term ConId Void) Proof
  deriving (Show)
