--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Cut.agda
--------------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLCPS.ResMon.Cut {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NLCPS.Type                               Atom as T
open import Logic.NLCPS.Type.Context.Polarised             Atom as TCP using ([])
open import Logic.NLCPS.ResMon.Sequent                   Atom
open import Logic.NLCPS.ResMon.Sequent.Context.Polarised Atom as JCP
open import Logic.NLCPS.ResMon.Base                        Atom as NLCPSB
open import Logic.NLCPS.ResMon.Origin                      Atom as NLCPSO


cut′ : ∀ {A B C} (f : NLCPS A ⊢ B) (g : NLCPS B ⊢ C) → NLCPS A ⊢ C

cut′ {B = el B}      f  g with el.view ([] <⊢ _) g
... | el.origin         g′ _ = g′ f

cut′ {B = ◇ B}       f  g with ◇₁.view (_ ⊢> []) f
... | ◇₁.origin h₁   f′ _ with ◇₂.view ([] <⊢ _) g
... | ◇₂.origin h₂      g′ _ = f′ (g′ (m◇ (cut′ h₁ h₂)))

cut′ {B = B₁ ⊗ B₂}   f  g with ⊗.view (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′    _ = f′ (r⇐⊗ (cut′ h₁ (r⇒⇐′ (cut′ h₂ (r⊗⇒ g)))))

cut′ {B = B₁ ⇐ B₂}   f  g with ⇐.view ([] <⊢ _) g
... | ⇐.origin h₁ h₂    g′ _ = g′ (r⇒⇐′ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁))))

cut′ {B = B₁ ⇒ B₂}   f  g with ⇒.view ([] <⊢ _) g
... | ⇒.origin h₁ h₂    g′ _ = g′ (r⇐⇒′ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂))))
