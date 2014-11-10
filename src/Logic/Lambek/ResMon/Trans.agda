------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Lambek.ResMon.Trans {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Lambek.Type                               Univ as T
open import Logic.Lambek.Type.Context.Polarised             Univ as TCP using ([])
open import Logic.Lambek.ResMon.Judgement                   Univ as J
open import Logic.Lambek.ResMon.Judgement.Context.Polarised Univ as JCP
open import Logic.Lambek.ResMon.Base                        Univ as RMB
open import Logic.Lambek.ResMon.Derivation                  Univ as RMD
open import Logic.Lambek.ResMon.Origin                      Univ as RMO


open RMD.Simple renaming (_[_] to _[_]ᴰ)


trans′ : ∀ {A B C} (f : NL A ⊢ B) (g : NL B ⊢ C) → NL A ⊢ C
trans′ {B = el B}    f g with el.viewOrigin ([] <⊢ _) g
... | el.origin      g′ _ = g′ [ f ]ᴰ
trans′ {B = B₁ ⊗ B₂} f g with ⊗.viewOrigin (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ [ res-⇐⊗ (trans′ h₁ (res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ g))))) ]ᴰ
trans′ {B = B₁ ⇐ B₂} f g with ⇐.viewOrigin ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ [ res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ (trans′ (res-⇐⊗ f) h₁)))) ]ᴰ
trans′ {B = B₁ ⇒ B₂} f g with ⇒.viewOrigin ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ [ res-⊗⇒ (res-⇐⊗ (trans′ h₁ (res-⊗⇐ (trans′ (res-⇒⊗ f) h₂)))) ]ᴰ
