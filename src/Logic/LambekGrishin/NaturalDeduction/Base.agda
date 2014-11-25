------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.LambekGrishin.NaturalDeduction.Base {ℓ} (Univ : Set ℓ) where


open import Logic.LambekGrishin.Type                   Univ as T
open import Logic.LambekGrishin.Type.Context           Univ as TC
open import Logic.LambekGrishin.Type.Context.Polarised Univ as TCP
open import Logic.LambekGrishin.ResMon.Judgement       Univ as NDJ
open TC.Simple using (_[_])


infix 3 LG_

data LG_ : Judgement → Set ℓ where
  id : ∀ {A}       → LG A ⊢ A

  ⊗I : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⊗ C ⊢ B ⊗ D
  ⊗E : ∀ {A B C D} → LG A ⊢ B ⊗ C → LG B ⊗ C ⊢ D → LG A ⊢ D
  ⇒I : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG B ⊢ A ⇒ C
  ⇒E : ∀ {A B C D} → LG A ⊢ C     → LG B ⊢ C ⇒ D → LG A ⊗ B ⊢ D
  ⇐I : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG A ⊢ C ⇐ B
  ⇐E : ∀ {A B C D} → LG A ⊢ D ⇐ C → LG B ⊢ C     → LG A ⊗ B ⊢ D




{-
trans′ : ∀ {A B C} → NL A ⊢ B → NL B ⊢ C → NL A ⊢ C
trans′ f id         = f
trans′ f (⊗I g₁ g₂) = ⊗E f (⊗I g₁ g₂)
trans′ f (⊗E g₁ g₂) = ⊗E (trans′ f g₁) g₂
trans′ f (⇒I g)     = ⇒I (⇐E (⇐I g) f)
trans′ f (⇒E g₁ g₂) = ⊗E f (⇒E g₁ g₂)
trans′ f (⇐I g)     = ⇐I (⇒E f (⇒I g))
trans′ f (⇐E g₁ g₂) = ⊗E f (⇐E g₁ g₂)
-}
