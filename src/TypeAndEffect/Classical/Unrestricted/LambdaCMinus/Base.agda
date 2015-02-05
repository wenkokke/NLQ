------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.List using (List; _++_) renaming ([] to ∅; _∷_ to _,_)


module TypeAndEffect.Classical.Unrestricted.LambdaCMinus.Base {ℓ} (Univ : Set ℓ) where


open import TypeAndEffect.Type      Univ
open import TypeAndEffect.Judgement Univ


infix 1 λC⁻_

data λC⁻_ : Judgement → Set ℓ where

  ax   : ∀ {Γ A T Δ}
       → λC⁻ A ,   Γ ^ T   ⊢[  A ^ T                 ] Δ

  ⇒ᵢ   : ∀ {Γ A B T₁ T₂ T₃ Δ}
       → λC⁻ A ,   Γ  ^ T₁ ⊢[           B ^ T₂       ] Δ
       → λC⁻       Γ  ^ T₃ ⊢[ (A ^ T₁ ⇒ B ^ T₂) ^ T₃ ] Δ

  ⇒ₑ   : ∀ {Γ₁ Γ₂ A B U₁ U₂ T₁ T₂ Δ}
       → λC⁻ Γ₁       ^ U₁ ⊢[ (A ^ U₂ ⇒ B ^ T₁) ^ T₂ ] Δ
       → λC⁻       Γ₂ ^ T₁ ⊢[  A ^ U₁                ] Δ
       → λC⁻ Γ₁ ++ Γ₂ ^ U₂ ⊢[           B ^ T₂       ] Δ

  raa  : ∀ {Γ A T U Δ}
       → λC⁻ Γ     ⊢         (¬ A ^ U , Δ) ^ T
       → λC⁻ Γ ^ U ⊢[ A ^ T ]         Δ

  raaᵀ : ∀ {Γ A T Δ}
       → λC⁻ Γ     ⊢          Δ ^ A
       → λC⁻ Γ ^ T ⊢[ A ^ T ] Δ

  ⇒ₑᵏ  : ∀ {Γ A T U Δ}
       → λC⁻ Γ ^ U ⊢[ A ^ T ] ¬ A ^ U , Δ
       → λC⁻ Γ     ⊢         (¬ A ^ U , Δ) ^ T

  ⇒ₑᵏᵀ : ∀ {Γ T U Δ}
       → λC⁻ Γ ^ U ⊢[ U ^ T ] Δ
       → λC⁻ Γ     ⊢          Δ ^ T
