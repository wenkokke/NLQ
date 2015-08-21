------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NLIBC.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type Atom


infixr 20 _∙_
infixr 20 _∘_


data Structure : Set ℓ where
  ·_·  : Type      → Structure
  _∙_  : Structure → Structure → Structure
  _∘_  : Structure → Structure → Structure
  I    : Structure
  B    : Structure
  C    : Structure
