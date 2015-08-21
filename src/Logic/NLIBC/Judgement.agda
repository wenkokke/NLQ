------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NLIBC.Judgement {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type                 Atom
open import Logic.NLIBC.Structure         Atom


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : Structure → Type → Judgement
