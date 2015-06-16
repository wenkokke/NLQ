------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level        using (suc)
open import Function     using (case_of_; _∘_) renaming (id to λΠ_)
open import Data.List    using (List; _∷_; map)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Intuitionistic.Unrestricted.Lambda.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) where


open import Logic.Translation
open import Logic.Intuitionistic.Linear.Lambda.Type       Univ
open import Logic.Intuitionistic.Linear.Lambda.Judgement  Univ
open import Logic.Intuitionistic.Unrestricted.Lambda.Base Univ
open import Logic.Intuitionistic.Unrestricted.Agda.Environment


private
  ⟦_⟧ᵀ : Type → Set ℓ₂
  ⟦ el  A ⟧ᵀ = ⟦ A ⟧ᵁ
  ⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ → ⟦ B ⟧ᵀ
  ⟦ A ⊗ B ⟧ᵀ = ⟦ A ⟧ᵀ × ⟦ B ⟧ᵀ

  ⟦_⟧ˢ : List Type → List (Set ℓ₂)
  ⟦_⟧ˢ = map ⟦_⟧ᵀ

  ⟦_⟧ᴶ : Judgement → Set (suc ℓ₂)
  ⟦ Γ ⊢ A ⟧ᴶ = Env ⟦ Γ ⟧ˢ → ⟦ A ⟧ᵀ

  [_] : ∀ {J} → Λ J → λΠ ⟦ J ⟧ᴶ
  [ ax               ] (x ∷ ∅) = x
  [ ⇒ᵢ f             ]      e  = λ x → [ f ] (x ∷ e)
  [ ⇒ₑ f g           ]      e  = split e into λ e₁ e₂ → [ f ] e₁  ([ g ] e₂)
  [ ⊗ᵢ f g           ]      e  = split e into λ e₁ e₂ → [ f ] e₁ , [ g ] e₂
  [ ⊗ₑ f g           ]      e  = split e into λ e₁ e₂ → case [ f ] e₁ of (λ {(x , y) → [ g ] (x ∷ (y ∷ e₂))})
  [ wᴸ₁ f            ] (_ ∷ e) = [ f ] e
  [ cᴸ₁ f            ] (x ∷ e) = [ f ] (x ∷ (x ∷ e))
  [ eᴸ Γ₁ Γ₂ Γ₃ Γ₄ f ]      e  = [ f ] (exchange Γ₁ Γ₃ Γ₂ Γ₄ e)


Λ→ΛΠ : Translation Type (Set ℓ₂) Λ_ λΠ_
Λ→ΛΠ = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
