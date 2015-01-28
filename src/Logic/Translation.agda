open import Level    using (suc; _⊔_)
open import Function using (_∘_)


module Logic.Translation where


record Translation {j₁ j₂ t₁ t₂} {Judgement₁ : Set j₁} {Judgement₂ : Set j₂} (Term₁ : Judgement₁ → Set t₁) (Term₂ : Judgement₂ → Set t₂) : Set (suc (j₁ ⊔ j₂ ⊔ t₁ ⊔ t₂)) where
  field
    ⟦_⟧ : Judgement₁ → Judgement₂
    [_] : {J : Judgement₁} → Term₁ J → Term₂ ⟦ J ⟧


_◇_ : ∀ {j₁ j₂ j₃ t₁ t₂ t₃}
        {J₁ : Set j₁} {J₂ : Set j₂} {J₃ : Set j₃}
        {T₁ : J₁ → Set t₁} {T₂ : J₂ → Set t₂} {T₃ : J₃ → Set t₃}
        → Translation T₁ T₂ → Translation T₂ T₃ → Translation T₁ T₃
f ◇ g = record
  { ⟦_⟧ = Translation.⟦ g ⟧ ∘ Translation.⟦ f ⟧
  ; [_] = Translation.[ g ] ∘ Translation.[ f ] }
