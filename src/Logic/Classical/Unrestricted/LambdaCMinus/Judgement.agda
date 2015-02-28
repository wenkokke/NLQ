------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.List                                  using (List)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Unrestricted.LambdaCMinus.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Unrestricted.LambdaCMinus.Type Univ


infixr 3 _⊢_ _⊢[_]_


data Judgement : Set ℓ where
  _⊢_    : List Type        → List Type → Judgement
  _⊢[_]_ : List Type → Type → List Type → Judgement


ante : Judgement → List Type
ante (Γ ⊢      _) = Γ
ante (Γ ⊢[ _ ] _) = Γ

succ : Judgement → List Type
succ (_ ⊢      Δ) = Δ
succ (_ ⊢[ _ ] Δ) = Δ

⊢-injective : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → (Γ₁ ⊢ Γ₂) ≡ (Γ₃ ⊢ Γ₄) → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
⊢-injective refl = refl , refl

⊢[]-injective : ∀ {A B Γ₁ Γ₂ Δ₁ Δ₂} → (Γ₁ ⊢[ A ] Δ₁) ≡ (Γ₂ ⊢[ B ] Δ₂) → Γ₁ ≡ Γ₂ × A ≡ B × Δ₁ ≡ Δ₂
⊢[]-injective refl = refl , refl , refl
