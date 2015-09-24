------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NL.SC.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type Atom


infixr 4 _,_


data Structure : Set ℓ where
  ·_·  : (A : Type) → Structure
  _,_  : (Γ Δ : Structure) → Structure
