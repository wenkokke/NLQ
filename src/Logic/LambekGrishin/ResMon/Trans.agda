------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.LambekGrishin.ResMon.Trans {ℓ} (Univ : Set ℓ) where


open import Logic.LambekGrishin.Type                   Univ as LGT
open import Logic.LambekGrishin.Type.Context           Univ as LGC
open import Logic.LambekGrishin.Type.Context.Polarised Univ as LGCP
open import Logic.LambekGrishin.ResMon.Base            Univ as LGB
open import Logic.LambekGrishin.ResMon.Derivation      Univ as LGD
open import Logic.LambekGrishin.ResMon.Origin          Univ as LGO
open LGD.Simple using () renaming (_[_] to _[_]ᴰ)


open import Logic.Judgement Type Type using (_⊢_)
open import Logic.Judgement.Context
  Type Context LGC.Simple._[_] LGC.Simple._<_>
  as JC using () renaming (_[_] to _[_]ᴶ)
open import Logic.Judgement.Context.Polarised
  Type Context LGC.Simple._[_] LGC.Simple._<_>
  Polarised LGCP.Simple._[_] LGCP.Simple._<_>
  using (_⊢>_; _<⊢_)


trans′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el B}    f g with el.viewOrigin ([] <⊢ _) g
... | el.origin      g′ _ = g′ [ f ]ᴰ
trans′ {B = B₁ ⊗ B₂} f g with ⊗.viewOrigin (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ [ res-⇐⊗ (trans′ h₁ (res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ g))))) ]ᴰ
trans′ {B = B₁ ⇚ B₂} f g with ⇚.viewOrigin (_ ⊢> []) f
... | ⇚.origin h₁ h₂ f′ _ = f′ [ res-⊕⇚ (res-⇛⊕ (trans′ (res-⊕⇛ (trans′ h₁ (res-⇚⊕ g))) h₂)) ]ᴰ
trans′ {B = B₁ ⇛ B₂} f g with ⇛.viewOrigin (_ ⊢> []) f
... | ⇛.origin h₁ h₂ f′ _ = f′ [ res-⊕⇛ (res-⇚⊕ (trans′ (res-⊕⇚ (trans′ h₁ (res-⇛⊕ g))) h₂)) ]ᴰ
trans′ {B = B₁ ⊕ B₂} f g with ⊕.viewOrigin ([] <⊢ _) g
... | ⊕.origin h₁ h₂ g′ _ = g′ [ res-⇚⊕ (trans′ (res-⊕⇚ (res-⇛⊕ (trans′ (res-⊕⇛ f) h₂))) h₁) ]ᴰ
trans′ {B = B₁ ⇐ B₂} f g with ⇐.viewOrigin ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ [ res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ (trans′ (res-⇐⊗ f) h₁)))) ]ᴰ
trans′ {B = B₁ ⇒ B₂} f g with ⇒.viewOrigin ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ [ res-⊗⇒ (res-⇐⊗ (trans′ h₁ (res-⊗⇐ (trans′ (res-⇒⊗ f) h₂)))) ]ᴰ
