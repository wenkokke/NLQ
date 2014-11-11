------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------y


module Logic.Linear.NaturalDeduction.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Linear.Type                       Univ as T
open import Logic.Linear.NaturalDeduction.Judgement Univ as NDJ


infix 3 LP_

data LP_ : Judgement → Set ℓ where
  id   : ∀ {A}       → LP A ⊢ A
  ⊗I   : ∀ {A B C D} → LP A ⊢ B           → LP C ⊢ D     → LP A ⊗ C ⊢ B ⊗ D
  ⊗E   : ∀ {A B C D} → LP A ⊢ B ⊗ C       → LP B ⊗ C ⊢ D → LP A ⊢ D
  ⊸I   : ∀ {A B C}   → LP A ⊗ B ⊢ C       → LP B ⊢ A ⊸ C
  ⊸E   : ∀ {A B C D} → LP A ⊢ C           → LP B ⊢ C ⊸ D → LP A ⊗ B ⊢ D
  ass₁ : ∀ {A B C D} → LP (A ⊗ B) ⊗ C ⊢ D → LP A ⊗ (B ⊗ C) ⊢ D
  ass₂ : ∀ {A B C D} → LP A ⊗ (B ⊗ C) ⊢ D → LP (A ⊗ B) ⊗ C ⊢ D
  comm : ∀ {A B C}   → LP A ⊗ B ⊢ C       → LP B ⊗ A ⊢ C
