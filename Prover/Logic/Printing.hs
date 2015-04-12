{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}
module Logic.Printing where


import           Prover hiding (Term)
import qualified Prover
import           Logic.Base


newtype ASCII a = ASCII a

instance Show (ASCII ConId) where
  show (ASCII FProd  ) = "*" ; show (ASCII FImpR  ) = "->"; show (ASCII FImpL  ) = "<-"
  show (ASCII SProd  ) = "*" ; show (ASCII SImpR  ) = "->"; show (ASCII SImpL  ) = "<-"
  show (ASCII FPlus  ) = "+" ; show (ASCII FSubL  ) = "<="; show (ASCII FSubR  ) = "=>"
  show (ASCII SPlus  ) = "+" ; show (ASCII SSubL  ) = "<="; show (ASCII SSubR  ) = "=>"
  show (ASCII JStruct) = "|-"; show (ASCII JFocusL) = "|-"; show (ASCII JFocusR) = "|-"
  show (ASCII Down   ) = "."


instance Show ConId where
  show  FProd   = "⊗"; show  FImpR   = "⇒"; show  FImpL   = "⇐"
  show  SProd   = "⊗"; show  SImpR   = "⇒"; show  SImpL   = "⇐"
  show  FPlus   = "⊕"; show  FSubL   = "⇚"; show  FSubR   = "⇛";
  show  SPlus   = "⊕"; show  SSubL   = "⇚"; show  SSubR   = "⇛";
  show  JStruct = "⊢"; show  JFocusL = "⊢"; show  JFocusR = "⊢";
  show  Down    = "·"


prec :: ConId -> Int
prec FProd = 8; prec FImpR = 7; prec FImpL = 7
prec FPlus = 8; prec FSubL = 7; prec FSubR = 7
prec SProd = 5; prec SImpR = 4; prec SImpL = 4
prec SPlus = 5; prec SSubL = 4; prec SSubR = 4


instance (Show v) => Show (Term v) where
  showsPrec _ (Var i) = shows i
  showsPrec _ (Con (Atom x) [])     = showString x
  showsPrec _ (Con Down [x])        =
    shows Down . showChar ' ' . shows x . showChar ' ' . shows Down
  showsPrec _ (Con f@JStruct [x,y]) =
    showsPrec 3 x . showChar ' ' . shows f . showChar ' ' . showsPrec 3 y
  showsPrec _ (Con f@JFocusL [a,y]) =
    showString "[ " . showsPrec 3 a . showString " ]" . shows f . showChar ' ' . showsPrec 3 y
  showsPrec _ (Con f@JFocusR [x,b]) =
    showsPrec 3 x . showChar ' ' . shows f . showString "[ " . showsPrec 3 b . showString " ]"
  showsPrec p (Con f [x,y])       = let q = prec f in
    showParen (p >= q) $
      showsPrec q x . showChar ' ' . shows f . showChar ' ' . showsPrec q y


instance (Show v) => Show (Prover.Term (ASCII ConId) v) where
  showsPrec _ (Con (ASCII (Atom x)) [])     = showString x
  showsPrec p (Con (ASCII Down) [x])        =
    shows Down . showChar ' ' . showsPrec p x . showChar ' ' . shows Down
  showsPrec _ (Con f@(ASCII JStruct) [x,y]) =
    showsPrec 3 x . showChar ' ' . shows f . showChar ' ' . showsPrec 3 y
  showsPrec _ (Con f@(ASCII JFocusL) [a,y]) =
    showString "[ " . showsPrec 3 a . showString " ]" . shows f . showChar ' ' . showsPrec 3 y
  showsPrec _ (Con f@(ASCII JFocusR) [x,b]) =
    showsPrec 3 x . showChar ' ' . shows f . showString "[ " . showsPrec 3 b . showString " ]"
  showsPrec p (Con (ASCII f) [x,y])       = let q = prec f in
    showParen (p >= q) $
      showsPrec q x . showChar ' ' . shows (ASCII f) . showChar ' ' . showsPrec q y


instance Show Proof where
  showsPrec p (Con f []) = showString f
  showsPrec p (Con f xs) =
    showParen (p >= 1) $ showString f . showSeq (showsPrec 1) xs
    where
      showSeq _  []     = id
      showSeq ss (x:xs) = showChar ' ' . ss x . showSeq ss xs
