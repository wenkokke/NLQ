open import Data.List using (List; map; length; _++_) renaming ([] to ·; _∷_ to _,_)


module Logic.Classical.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Type      Univ
open import Logic.Structure Univ


infix 2 [_⟩_ _⟨_]
infix 3 _⊢_ _⊢[_]_


data Judgement : Set ℓ where
  _⊢_    : Structure →        Structure → Judgement
  _⊢[_]_ : Structure → Type → Structure → Judgement


data [_⟩_ : Structure → Judgement → Set ℓ where
  refl  : ∀ {Γ A Δ} → [ Γ ⟩ Γ ⊢[ A ] Δ
  refl′ : ∀ {Γ   Δ} → [ Γ ⟩ Γ ⊢      Δ


data _⟨_] : Judgement → Structure → Set ℓ where
  refl  : ∀ {Γ A Δ} → Γ ⊢[ A ] Δ ⟨ Δ ]
  refl′ : ∀ {Γ   Δ} → Γ ⊢      Δ ⟨ Δ ]


⊢₁ : Judgement → Structure
⊢₁ (Γ ⊢      _) = Γ
⊢₁ (Γ ⊢[ _ ] _) = Γ

⊢₂ : Judgement → Structure
⊢₂ (_ ⊢      Δ) = Δ
⊢₂ (_ ⊢[ _ ] Δ) = Δ
