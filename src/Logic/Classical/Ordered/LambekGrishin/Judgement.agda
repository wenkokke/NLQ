------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambekGrishin.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type Univ


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement
