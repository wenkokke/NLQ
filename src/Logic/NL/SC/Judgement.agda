------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NL.SC.Judgement {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type                 Atom
open import Logic.NL.SC.Structure         Atom


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : Structure → Type → Judgement
