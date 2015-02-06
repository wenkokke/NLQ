------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level using (_⊔_)


module Logic.Judgement {ℓ₁ ℓ₂ ℓ₃} (Anta : Set ℓ₁) (Type : Set ℓ₂) (Succ : Set ℓ₃) where


infix 3 _⊢_ _⊢[_]_


data Judgement : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
  _⊢_    : Anta →        Succ → Judgement
  _⊢[_]_ : Anta → Type → Succ → Judgement



anta : Judgement → Anta
anta (Γ ⊢      _) = Γ
anta (Γ ⊢[ _ ] _) = Γ

succ : Judgement → Succ
succ (_ ⊢      Δ) = Δ
succ (_ ⊢[ _ ] Δ) = Δ
