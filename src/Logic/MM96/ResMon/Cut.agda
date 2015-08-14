--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Cut.agda
--------------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.MM96.ResMon.Cut {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.MM96.Type                               Atom as T
open import Logic.MM96.Type.Context.Polarised             Atom as TCP using ([])
open import Logic.MM96.ResMon.Judgement                   Atom
open import Logic.MM96.ResMon.Judgement.Context.Polarised Atom as JCP
open import Logic.MM96.ResMon.Base                        Atom as MM96B
open import Logic.MM96.ResMon.Origin                      Atom as MM96O


cut′ : ∀ {A B C} (f : MM96 A ⊢ B) (g : MM96 B ⊢ C) → MM96 A ⊢ C
cut′ {B = el B}    f  g with el.view ([] <⊢ _) g
... | el.origin      g′ _ = g′ f
cut′ {B = ⟨l⟩ B}     f  g with ⟨l⟩.view ([] <⊢ _) g
... | ⟨l⟩.origin h     g′ _ = g′ (r⟨r⟩⟨l⟩ (cut′ (r⟨l⟩⟨r⟩ f) h))
cut′ {B = ⟨r⟩ B}     f  g with ⟨r⟩.view (_ ⊢> []) f
... | ⟨r⟩.origin h     f′ _ = f′ (r⟨l⟩⟨r⟩ (cut′ h (r⟨r⟩⟨l⟩ g)))
cut′ {B = B₁ ⊗ B₂} f  g with ⊗.view (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ (r⇐⊗ (cut′ h₁ (r⇒⇐′ (cut′ h₂ (r⊗⇒ g)))))
cut′ {B = B₁ ⇦ B₂} f  g with ⇦.view (_ ⊢> []) f
... | ⇦.origin h₁ h₂ f′ _ = f′ (r⇨⇦′ (cut′ (r⊙⇨ (cut′ h₁ (r⇦⊙ g))) h₂))
cut′ {B = B₁ ⇨ B₂} f  g with ⇨.view (_ ⊢> []) f
... | ⇨.origin h₁ h₂ f′ _ = f′ (r⇦⇨′ (cut′ (r⊙⇦ (cut′ h₂ (r⇨⊙ g))) h₁))
cut′ {B = B₁ ⊙ B₂} f  g with ⊙.view ([] <⊢ _) g
... | ⊙.origin h₁ h₂ g′ _ = g′ (r⇦⊙ (cut′ (r⇨⇦′ (cut′ (r⊙⇨ f) h₂)) h₁))
cut′ {B = B₁ ⇐ B₂} f  g with ⇐.view ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ (r⇒⇐′ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁))))
cut′ {B = B₁ ⇒ B₂} f  g with ⇒.view ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ (r⇐⇒′ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂))))
