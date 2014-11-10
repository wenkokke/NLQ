------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements the axioms and some derived inference rules.
------------------------------------------------------------------------


module Logic.Lambek.SC.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type         Univ as T
open import Logic.Lambek.Type.Context Univ as TC
open TC.Simple using (_[_]; _<_>; <>-assoc; <>-def)


infix 5 _⊢_ ⊢ᴺ_ ⊢ᴾ_

data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement
  ⊢ᴺ_ : Context → Judgement
  ⊢ᴾ_ : Context → Judgement
