------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Empty using (⊥)


module Logic.Classical.Ordered.LambekGrishin.ResMon.Trans {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                               Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised             Univ as TCP using ([])
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement                   Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.Context.Polarised Univ as JCP
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base                        Univ as LGB
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Derivation                  Univ as LGD
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Origin                      Univ as LGO


open LGD.Simple using (_[_])


trans′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el B}    f g with el.viewOrigin ([] <⊢ _) g
... | el.origin      g′ _ = g′ [ f ]
trans′ {B = □ B}     f g with □.viewOrigin ([] <⊢ _) g
... | □.origin h     g′ _ = g′ [ res-◇□ (trans′ (res-□◇ f) h) ]
trans′ {B = ◇ B}     f g with ◇.viewOrigin (_ ⊢> []) f
... | ◇.origin h     f′ _ = f′ [ res-□◇ (trans′ h (res-◇□ g)) ]
trans′ {B = B₁ ⊗ B₂} f g with ⊗.viewOrigin (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ [ res-⇐⊗ (trans′ h₁ (res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ g))))) ]
trans′ {B = B₁ ⇚ B₂} f g with ⇚.viewOrigin (_ ⊢> []) f
... | ⇚.origin h₁ h₂ f′ _ = f′ [ res-⊕⇚ (res-⇛⊕ (trans′ (res-⊕⇛ (trans′ h₁ (res-⇚⊕ g))) h₂)) ]
trans′ {B = B₁ ⇛ B₂} f g with ⇛.viewOrigin (_ ⊢> []) f
... | ⇛.origin h₁ h₂ f′ _ = f′ [ res-⊕⇛ (res-⇚⊕ (trans′ (res-⊕⇚ (trans′ h₂ (res-⇛⊕ g))) h₁)) ]
trans′ {B = B₁ ⊕ B₂} f g with ⊕.viewOrigin ([] <⊢ _) g
... | ⊕.origin h₁ h₂ g′ _ = g′ [ res-⇚⊕ (trans′ (res-⊕⇚ (res-⇛⊕ (trans′ (res-⊕⇛ f) h₂))) h₁) ]
trans′ {B = B₁ ⇐ B₂} f g with ⇐.viewOrigin ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ [ res-⊗⇐ (res-⇒⊗ (trans′ h₂ (res-⊗⇒ (trans′ (res-⇐⊗ f) h₁)))) ]
trans′ {B = B₁ ⇒ B₂} f g with ⇒.viewOrigin ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ [ res-⊗⇒ (res-⇐⊗ (trans′ h₁ (res-⊗⇐ (trans′ (res-⇒⊗ f) h₂)))) ]
