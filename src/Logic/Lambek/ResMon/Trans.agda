------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------






module Logic.LambekGrishin.ResMon.Trans {ℓ} (Univ : Set ℓ) where






open import Logic.Type Univ
open import Logic.Type.Context.Polarised Univ using ([])
open import Logic.Judgement Type Type
open import Logic.Judgement.Context.Polarised Univ using (_<⊢_; _⊢>_)
open import Logic.LambekGrishin.ResMon.Base Univ
open import Logic.LambekGrishin.ResMon.Derivation Univ as LGD
open import Logic.LambekGrishin.ResMon.Origin Univ






open LGD.Simple using () renaming (_[_] to _[_]ᴰ)






trans′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el B}    f g with el.origin? ([] <⊢ _) g
... | el.origin      g′ _ = g′ [ f ]ᴰ
trans′ {B = B₁ ⊗ B₂} f g with ⊗.origin? (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ [ res-⇐⊗ (trans′ h₁ (res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ g))))) ]ᴰ
trans′ {B = B₁ ⇐ B₂} f g with ⇐.origin? ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ [ res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ (trans′ (res-⇐⊗ f) h₁)))) ]ᴰ
trans′ {B = B₁ ⇒ B₂} f g with ⇒.origin? ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ [ res-⊗⇒ (res-⇐⊗ (trans′ h₁ (res-⊗⇐ (trans′ (res-⇒⊗ f) h₂)))) ]ᴰ

