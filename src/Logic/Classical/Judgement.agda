open import Data.List using (List; map; length; _++_) renaming ([] to ·; _∷_ to _,_)


module Logic.Classical.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Type      Univ


infix 2 [_⟩_ _⟨_]
infix 3 _⊢_ _⊢[_]_


data Judgement : Set ℓ where
  _⊢_    : List Type →        List Type → Judgement
  _⊢[_]_ : List Type → Type → List Type → Judgement


data [_⟩_ : List Type → Judgement → Set ℓ where
  refl  : ∀ {Γ A Δ} → [ Γ ⟩ Γ ⊢[ A ] Δ
  refl′ : ∀ {Γ   Δ} → [ Γ ⟩ Γ ⊢      Δ


data _⟨_] : Judgement → List Type → Set ℓ where
  refl  : ∀ {Γ A Δ} → Γ ⊢[ A ] Δ ⟨ Δ ]
  refl′ : ∀ {Γ   Δ} → Γ ⊢      Δ ⟨ Δ ]


⊢ᴸ : Judgement → List Type
⊢ᴸ (Γ ⊢      _) = Γ
⊢ᴸ (Γ ⊢[ _ ] _) = Γ

⊢ᴿ : Judgement → List Type
⊢ᴿ (_ ⊢      Δ) = Δ
⊢ᴿ (_ ⊢[ _ ] Δ) = Δ
