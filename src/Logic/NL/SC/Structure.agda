------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NL.SC.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type Atom


infixr 5 _,_


data Structure : Set ℓ where
  ·_·  : Type      → Structure
  _,_  : Structure → Structure → Structure
