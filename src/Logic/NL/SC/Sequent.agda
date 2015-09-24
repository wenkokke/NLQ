------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NL.SC.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type                 Atom
open import Logic.NL.SC.Structure         Atom


infix 3 _⊢_


data Sequent : Set ℓ where
  _⊢_ : (Γ : Structure) (A : Type) → Sequent
