------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Linear.LambekGrishin.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Linear.LambekGrishin.Type Univ


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement
