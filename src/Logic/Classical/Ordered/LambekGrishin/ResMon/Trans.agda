------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


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
trans′ {B = el B}    f  g with el.viewOrigin ([] <⊢ _) g
... | el.origin      g′ _ = g′ [ f ]
trans′ {B = □ B}     f  g with □.viewOrigin ([] <⊢ _) g
... | □.origin h     g′ _ = g′ [ r◇□ (trans′ (r□◇ f) h) ]
trans′ {B = ◇ B}     f  g with ◇.viewOrigin (_ ⊢> []) f
... | ◇.origin h     f′ _ = f′ [ r□◇ (trans′ h (r◇□ g)) ]
trans′ {B = ₀ B}     f  g with ₀.viewOrigin ([] <⊢ _) g
... | ₀.origin h     g′ _ = g′ [ r⁰₀ (trans′ h (r₀⁰ f)) ]
trans′ {B = B ⁰}     f  g with ⁰.viewOrigin ([] <⊢ _) g
... | ⁰.origin h     g′ _ = g′ [ r₀⁰ (trans′ h (r⁰₀ f)) ]
trans′ {B = ₁ B}     f  g with ₁.viewOrigin (_ ⊢> []) f
... | ₁.origin h     f′ _ = f′ [ r¹₁ (trans′ (r₁¹ g) h) ]
trans′ {B = B ¹}     f  g with ¹.viewOrigin (_ ⊢> []) f
... | ¹.origin h     f′ _ = f′ [ r₁¹ (trans′ (r¹₁ g) h) ]
trans′ {B = B₁ ⊗ B₂} f  g with ⊗.viewOrigin (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ [ r⇐⊗ (trans′ h₁ (r⇒⇐′ (trans′ h₂ (r⊗⇒ g)))) ]
trans′ {B = B₁ ⇚ B₂} f  g with ⇚.viewOrigin (_ ⊢> []) f
... | ⇚.origin h₁ h₂ f′ _ = f′ [ r⇛⇚′ (trans′ (r⊕⇛ (trans′ h₁ (r⇚⊕ g))) h₂) ]
trans′ {B = B₁ ⇛ B₂} f  g with ⇛.viewOrigin (_ ⊢> []) f
... | ⇛.origin h₁ h₂ f′ _ = f′ [ r⇚⇛′ (trans′ (r⊕⇚ (trans′ h₂ (r⇛⊕ g))) h₁) ]
trans′ {B = B₁ ⊕ B₂} f  g with ⊕.viewOrigin ([] <⊢ _) g
... | ⊕.origin h₁ h₂ g′ _ = g′ [ r⇚⊕ (trans′ (r⇛⇚′ (trans′ (r⊕⇛ f) h₂)) h₁) ]
trans′ {B = B₁ ⇐ B₂} f  g with ⇐.viewOrigin ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ [ r⇒⇐′ (trans′ h₂ (r⊗⇒ (trans′ (r⇐⊗ f) h₁))) ]
trans′ {B = B₁ ⇒ B₂} f  g with ⇒.viewOrigin ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ [ r⇐⇒′ (trans′ h₁ (r⊗⇐ (trans′ (r⇒⊗ f) h₂))) ]
