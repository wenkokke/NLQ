------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------y


module Logic.Lambek.NaturalDeduction.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type             Univ as T
open import Logic.Lambek.ResMon.Judgement Univ as NDJ


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
