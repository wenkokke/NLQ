------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.ResMon.Trans {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                               Atom as T
open import Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised             Atom as TCP using ([])
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement                   Atom
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.Context.Polarised Atom as JCP
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base                        Atom as LGB
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Origin                      Atom as LGO


cut′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
cut′ {B = el B}    f  g with el.viewOrigin ([] <⊢ _) g
... | el.origin      g′ _ = g′ f
cut′ {B = □ B}     f  g with □.viewOrigin ([] <⊢ _) g
... | □.origin h     g′ _ = g′ (r◇□ (cut′ (r□◇ f) h))
cut′ {B = ◇ B}     f  g with ◇.viewOrigin (_ ⊢> []) f
... | ◇.origin h     f′ _ = f′ (r□◇ (cut′ h (r◇□ g)))
cut′ {B = ₀ B}     f  g with ₀.viewOrigin ([] <⊢ _) g
... | ₀.origin h     g′ _ = g′ (r⁰₀ (cut′ h (r₀⁰ f)))
cut′ {B = B ⁰}     f  g with ⁰.viewOrigin ([] <⊢ _) g
... | ⁰.origin h     g′ _ = g′ (r₀⁰ (cut′ h (r⁰₀ f)))
cut′ {B = ₁ B}     f  g with ₁.viewOrigin (_ ⊢> []) f
... | ₁.origin h     f′ _ = f′ (r¹₁ (cut′ (r₁¹ g) h))
cut′ {B = B ¹}     f  g with ¹.viewOrigin (_ ⊢> []) f
... | ¹.origin h     f′ _ = f′ (r₁¹ (cut′ (r¹₁ g) h))
cut′ {B = B₁ ⊗ B₂} f  g with ⊗.viewOrigin (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ (r⇐⊗ (cut′ h₁ (r⇒⇐′ (cut′ h₂ (r⊗⇒ g)))))
cut′ {B = B₁ ⇚ B₂} f  g with ⇚.viewOrigin (_ ⊢> []) f
... | ⇚.origin h₁ h₂ f′ _ = f′ (r⇛⇚′ (cut′ (r⊕⇛ (cut′ h₁ (r⇚⊕ g))) h₂))
cut′ {B = B₁ ⇛ B₂} f  g with ⇛.viewOrigin (_ ⊢> []) f
... | ⇛.origin h₁ h₂ f′ _ = f′ (r⇚⇛′ (cut′ (r⊕⇚ (cut′ h₂ (r⇛⊕ g))) h₁))
cut′ {B = B₁ ⊕ B₂} f  g with ⊕.viewOrigin ([] <⊢ _) g
... | ⊕.origin h₁ h₂ g′ _ = g′ (r⇚⊕ (cut′ (r⇛⇚′ (cut′ (r⊕⇛ f) h₂)) h₁))
cut′ {B = B₁ ⇐ B₂} f  g with ⇐.viewOrigin ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ (r⇒⇐′ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁))))
cut′ {B = B₁ ⇒ B₂} f  g with ⇒.viewOrigin ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ (r⇐⇒′ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂))))
