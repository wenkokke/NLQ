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

  deriving (Eq,Ord,Show,Generic)


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

instance ToString ConId where
  toString (PosAtom x) = x
  toString (NegAtom x) = x ++ "⁻"
  toString F0L     = "₀"; toString F0R     = "⁰"; toString FBox  = "□"
  toString F1L     = "₁"; toString F1R     = "¹"; toString FDia  = "◇"
  toString FProd   = "⊗"; toString FImpR   = "⇒"; toString FImpL = "⇐"
  toString SProd   = "⊗"; toString SImpR   = "⇒"; toString SImpL = "⇐"
  toString HProd   = "∘"; toString HImpR   = "⇨"; toString HImpL = "⇦"
  toString FPlus   = "⊕"; toString FSubL   = "⇚"; toString FSubR = "⇛"
  toString SPlus   = "⊕"; toString SSubL   = "⇚"; toString SSubR = "⇛"
  toString S0L     = "₀"; toString S0R     = "⁰"; toString SBox  = "[]"
  toString S1L     = "₁"; toString S1R     = "¹"; toString SDia  = "⟨⟩"
  toString JAlgebr = "⊢"; toString JStruct = "⊢"
  toString JFocusL = "⊢"; toString JFocusR = "⊢"
  toString Down    = "·"; toString Comma   = ","

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

instance ToString (ASCII ConId) where
  toString (ASCII (PosAtom x)) = x
  toString (ASCII (NegAtom x)) = x ++ "'"
  toString (ASCII F0L)     = "0" ; toString (ASCII F0R)     = "0" ; toString (ASCII FBox)  = "[]"
  toString (ASCII F1L)     = "1" ; toString (ASCII F1R)     = "1" ; toString (ASCII FDia)  = "<>"
  toString (ASCII FProd)   = "*" ; toString (ASCII FImpR)   = "->"; toString (ASCII FImpL) = "<-"
  toString (ASCII SProd)   = "*" ; toString (ASCII SImpR)   = "->"; toString (ASCII SImpL) = "<-"
  toString (ASCII HProd)   = "o" ; toString (ASCII HImpR)   = "-o"; toString (ASCII HImpL) = "o-"
  toString (ASCII FPlus)   = "+" ; toString (ASCII FSubL)   = "<="; toString (ASCII FSubR) = "=>"
  toString (ASCII SPlus)   = "+" ; toString (ASCII SSubL)   = "<="; toString (ASCII SSubR) = "=>"
  toString (ASCII S0L)     = "0" ; toString (ASCII S0R)     = "0" ; toString (ASCII SBox)  = "[]"
  toString (ASCII S1L)     = "1" ; toString (ASCII S1R)     = "1" ; toString (ASCII SDia)  = "<>"
  toString (ASCII JAlgebr) = "|-"; toString (ASCII JStruct) = "|-"
  toString (ASCII JFocusL) = "|-"; toString (ASCII JFocusR) = "|-"
  toString (ASCII Down)    = "." ; toString (ASCII Comma)   = ","


-- * Proofs

type Proof = Term RuleId Void

data Result
  = Solved                 (Term ConId Void) Proof
  | Parsed String [String] (Term ConId Void) Proof
  deriving (Show)
