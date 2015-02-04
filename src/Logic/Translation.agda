------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level    using (suc; _⊔_)
open import Function using (_∘_)


module Logic.Translation {ℓ₁} (Univ : Set ℓ₁) where


open import Logic.Type Univ renaming (Type to Type₁)


record Translation {j₁ j₂ t₁ t₂ ℓ₂}
                   {Judgement₁ : Set j₁}
                   {Judgement₂ : Set j₂}
                   (Type₂ : Set ℓ₂)
                   (Term₁ : Judgement₁ → Set t₁)
                   (Term₂ : Judgement₂ → Set t₂)
                   : Set (suc (j₁ ⊔ j₂ ⊔ t₁ ⊔ t₂ ⊔ ℓ₁ ⊔ ℓ₂)) where
  field
    ⟦_⟧ᵀ : Type₁ → Type₂
    ⟦_⟧ᴶ : Judgement₁ → Judgement₂
    [_]  : {J : Judgement₁} → Term₁ J → Term₂ ⟦ J ⟧ᴶ


infixr 9 _◇_

_◇_ : ∀ {j₁ j₂ j₃ t₁ t₂ t₃ ℓ₂}
        {J₁    : Set j₁}
        {J₂    : Set j₂}
        {J₃    : Set j₃}
        {Type₂ : Set ℓ₂}
        {Tm₁   : J₁ → Set t₁}
        {Tm₂   : J₂ → Set t₂}
        {Tm₃   : J₃ → Set t₃}
        → Translation Type₂ Tm₂ Tm₃
        → Translation Type₁ Tm₁ Tm₂
        → Translation Type₂ Tm₁ Tm₃
f ◇ g = record
  { ⟦_⟧ᵀ = Translation.⟦ f ⟧ᵀ ∘ Translation.⟦ g ⟧ᵀ
  ; ⟦_⟧ᴶ = Translation.⟦ f ⟧ᴶ ∘ Translation.⟦ g ⟧ᴶ
  ; [_]  = Translation.[ f ]  ∘ Translation.[ g ] }
