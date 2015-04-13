{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module Logic.Printing where


import           Prover hiding (Term)
import qualified Prover ()
import           Logic.Base


-- |Return the precedence for the constructors.
prec :: ConId -> Int
prec F0L   = 9; prec F0R   = 9; prec FBox  = 9
prec F1L   = 9; prec F1R   = 9; prec FDia  = 9
prec FProd = 8; prec FImpR = 7; prec FImpL = 7
prec FPlus = 8; prec FSubL = 7; prec FSubR = 7
prec S0L   = 6; prec S0R   = 6; prec SBox  = 6
prec S1L   = 6; prec S1R   = 6; prec SDia  = 6
prec SProd = 5; prec SImpR = 4; prec SImpL = 4
prec SPlus = 5; prec SSubL = 4; prec SSubR = 4


data Fixity = Prefix | Suffix | Infix deriving (Eq)

-- |Return the fixity for the constructors.
fix :: ConId -> Fixity
fix F0L   = Prefix; fix F0R   = Suffix; fix FBox  = Prefix
fix F1L   = Prefix; fix F1R   = Suffix; fix FDia  = Prefix
fix FProd = Infix ; fix FImpR = Infix ; fix FImpL = Infix
fix FPlus = Infix ; fix FSubL = Infix ; fix FSubR = Infix
fix SProd = Infix ; fix SImpR = Infix ; fix SImpL = Infix
fix SPlus = Infix ; fix SSubL = Infix ; fix SSubR = Infix


-- * Agda representation

newtype Agda a = Agda a

instance Show (Agda ConId) where
  show (Agda F0L)   = "₀"; show (Agda F0R)   = "⁰"; show (Agda FBox)  = "□"
  show (Agda F1L)   = "₁"; show (Agda F1R)   = "¹"; show (Agda FDia)  = "◇"
  show (Agda FProd) = "⊗"; show (Agda FImpR) = "⇒"; show (Agda FImpL) = "⇐"
  show (Agda SProd) = "⊗"; show (Agda SImpR) = "⇒"; show (Agda SImpL) = "⇐"
  show (Agda FPlus) = "⊕"; show (Agda FSubL) = "⇚"; show (Agda FSubR) = "⇛"
  show (Agda SPlus) = "⊕"; show (Agda SSubL) = "⇚"; show (Agda SSubR) = "⇛"
  show (Agda S0L)   = "₀"; show (Agda S0R)   = "⁰"
  show (Agda S1L)   = "₁"; show (Agda S1R)   = "¹"
  show (Agda JForm)   = "⊢"; show (Agda JStruct) = "⊢"
  show (Agda JFocusL) = "⊢"; show (Agda JFocusR) = "⊢"
  show (Agda Down)    = "·"

instance (Show v) => Show (Agda (Term v)) where
  showsPrec _ (Agda (Var i)) = shows i
  showsPrec _ (Agda (Con (Atom x) []))
    = showNegAtom x
  showsPrec _ (Agda (Con Down [x]))
    = shows (Agda Down)
    . showChar ' '
    . shows (Agda x)
    . showChar ' '
    . shows (Agda Down)
  showsPrec _ (Agda (Con f@JStruct [x,y]))
    = showsPrec 3 (Agda x)
    . showChar ' '
    . shows (Agda f)
    . showChar ' '
    . showsPrec 3 (Agda y)
  showsPrec _ (Agda (Con f@JFocusL [a,y]))
    = showString "[ "
    . showsPrec 3 (Agda a)
    . showString " ]"
    . shows (Agda f)
    . showChar ' '
    . showsPrec 3 (Agda y)
  showsPrec _ (Agda (Con f@JFocusR [x,b]))
    = showsPrec 3 (Agda x)
    . showChar ' '
    . shows (Agda f)
    . showString "[ "
    . showsPrec 3 (Agda b)
    . showString " ]"
  showsPrec _ (Agda (Con SBox [x]))
    = showString "[ " . shows (Agda x) . showString " ]"
  showsPrec _ (Agda (Con SDia [x]))
    = showString "⟨ " . shows (Agda x) . showString " ⟩"
  showsPrec p (Agda (Con f [x]))
    | fix f == Prefix
    = let q = prec f in
       showParen (p >= q)
       $ shows (Agda f)
       . showChar ' '
       . showsPrec q (Agda x)
  showsPrec p (Agda (Con f [x]))
    | fix f == Suffix
    = let q = prec f in
       showParen (p >= q)
       $ showsPrec q (Agda x)
       . showChar ' '
       . shows (Agda f)
  showsPrec p (Agda (Con f [x,y]))
    | fix f == Infix
    = let q = prec f in
       showParen (p >= q)
       $ showsPrec q (Agda x)
       . showChar ' '
       . shows (Agda f)
       . showChar ' '
       . showsPrec q (Agda y)


-- * ASCII representation

newtype ASCII a = ASCII a

instance Show (ASCII ConId) where
  show (ASCII F0L)   = "0"; show (ASCII F0R)   = "0" ; show (ASCII FBox) = "[]"
  show (ASCII F1L)   = "1"; show (ASCII F1R)   = "1" ; show (ASCII FDia) = "<>"
  show (ASCII FProd) = "*"; show (ASCII FImpR) = "->"; show (ASCII FImpL) = "<-"
  show (ASCII SProd) = "*"; show (ASCII SImpR) = "->"; show (ASCII SImpL) = "<-"
  show (ASCII FPlus) = "+"; show (ASCII FSubL) = "<="; show (ASCII FSubR) = "=>"
  show (ASCII SPlus) = "+"; show (ASCII SSubL) = "<="; show (ASCII SSubR) = "=>"
  show (ASCII S0L)   = "0"; show (ASCII S0R)   = "0"
  show (ASCII S1L)   = "1"; show (ASCII S1R)   = "1"
  show (ASCII JForm)   = "|-"
  show (ASCII JStruct) = "|-"
  show (ASCII JFocusL) = "|-"
  show (ASCII JFocusR) = "|-"
  show (ASCII Down)    = "."

instance (Show v) => Show (ASCII (Term v)) where
  showsPrec _ (ASCII (Var i)) = shows i
  showsPrec _ (ASCII (Con (Atom x) []))
    = showNegAtom x
  showsPrec _ (ASCII (Con Down [x]))
    = shows (ASCII Down)
      . showChar ' '
      . shows (ASCII x)
      . showChar ' '
      . shows (ASCII Down)
  showsPrec _ (ASCII (Con f@JStruct [x,y]))
    = showsPrec 3 (ASCII x)
    . showChar ' '
    . shows (ASCII f)
    . showChar ' '
    . showsPrec 3 (ASCII y)
  showsPrec _ (ASCII (Con f@JFocusL [a,y]))
    = showString "[ "
    . showsPrec 3 (ASCII a)
    . showString " ]"
    . shows (ASCII f)
    . showChar ' '
    . showsPrec 3 (ASCII y)
  showsPrec _ (ASCII (Con f@JFocusR [x,b]))
    = showsPrec 3 (ASCII x)
    . showChar ' '
    . shows (ASCII f)
    . showString "[ "
    . showsPrec 3 (ASCII b)
    . showString " ]"
  showsPrec _ (ASCII (Con SBox [x]))
    = showString "[ " . shows (ASCII x) . showString " ]"
  showsPrec _ (ASCII (Con SDia [x]))
    = showString "< " . shows (ASCII x) . showString " >"
  showsPrec p (ASCII (Con f [x]))
    | fix f == Prefix
    = let q = prec f in
       showParen (p >= q)
       $ shows (ASCII f)
       . showChar ' '
       . showsPrec q (ASCII x)
  showsPrec p (ASCII (Con f [x]))
    | fix f == Suffix
    = let q = prec f in
       showParen (p >= q)
       $ showsPrec q (ASCII x)
       . showChar ' '
       . shows (ASCII f)
  showsPrec p (ASCII (Con f [x,y]))
    | fix f == Infix
    = let q = prec f in
       showParen (p >= q)
       $ showsPrec q (ASCII x)
       . showChar ' '
       . shows (ASCII f)
       . showChar ' '
       . showsPrec q (ASCII y)



-- |Show negative atoms, replacing any occurrence of @'@ with @⁻@.
showNegAtom :: String -> ShowS
showNegAtom str
  | last str == '\'' = showString (init str ++ "⁻")
  | otherwise        = showString str


-- |Show negative atoms, replacing any occurrence of @⁻@ with @'@.
showNegAtomASCII :: String -> ShowS
showNegAtomASCII str
  | last str == '⁻' = showString (init str ++ "'")
  | otherwise       = showString str
