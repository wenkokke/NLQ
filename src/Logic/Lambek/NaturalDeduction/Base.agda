------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Lambek.NaturalDeduction.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type                   Univ as T
open import Logic.Lambek.Type.Context           Univ as TC
open import Logic.Lambek.Type.Context.Polarised Univ as TCP
open import Logic.Lambek.ResMon.Judgement       Univ as NDJ
open TC.Simple using (_[_])


infix 3 NL_

data NL_ : Judgement → Set ℓ where
  id : ∀ {A}       → NL A ⊢ A
  ⊗I : ∀ {A B C D} → NL A ⊢ B     → NL C ⊢ D     → NL A ⊗ C ⊢ B ⊗ D
  ⊗E : ∀ {A B C D} → NL A ⊢ B ⊗ C → NL B ⊗ C ⊢ D → NL A ⊢ D
  ⇒I : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
  ⇒E : ∀ {A B C D} → NL A ⊢ C     → NL B ⊢ C ⇒ D → NL A ⊗ B ⊢ D
  ⇐I : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B
  ⇐E : ∀ {A B C D} → NL A ⊢ D ⇐ C → NL B ⊢ C     → NL A ⊗ B ⊢ D



trans′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
trans′ f id         = f
trans′ f (⊗I g₁ g₂) = ⊗E f (⊗I g₁ g₂)
trans′ f (⊗E g₁ g₂) = ⊗E (trans′ f g₁) g₂
trans′ f (⇒I g)     = ⇒I (⇐E (⇐I g) f)
trans′ f (⇒E g₁ g₂) = ⊗E f (⇒E g₁ g₂)
trans′ f (⇐I g)     = ⇐I (⇒E f (⇒I g))
trans′ f (⇐E g₁ g₂) = ⊗E f (⇐E g₁ g₂)


-- Simple proof showing that it is unnecessary to define the natural
-- deduction axiomatisation for the Lambek calculus with any sort of
-- reference to contexts, as the extended ⊗E′ rule becomes admissible
-- under a normal "context-free" axiomatisation.
⊗E′ : ∀ {Γ Δ A B C} → Structural Γ → NL Δ ⊢ A ⊗ B → NL Γ [ A ⊗ B ] ⊢ C → NL Γ [ Δ ] ⊢ C
⊗E′ []       f g = ⊗E f g
⊗E′ (_ ⊗> Γ) f g = ⇒E id (⊗E′ Γ f (⇒I g))
⊗E′ (Γ <⊗ _) f g = ⇒E (⊗E′ Γ f id) (⇒I g)
