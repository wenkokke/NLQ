--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Sequent.agda
--------------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLP.SC.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.SC.Type      Atom
open import Logic.NLP.SC.Structure Atom


infix  3  _⊢_
infixl 50 _⋈ʲ


data Sequent : Set ℓ where
  _⊢_ : Structure → Type → Sequent


_⋈ʲ : Sequent → Sequent
(Γ ⊢ B) ⋈ʲ = Γ ⋈ˢ ⊢ B ⋈ᵗ


open import Algebra.FunctionProperties {A = Sequent} _≡_


⋈ʲ-inv : Involutive _⋈ʲ
⋈ʲ-inv (Γ ⊢ B) rewrite ⋈ˢ-inv Γ | ⋈ᵗ-inv B = refl


⊢-injective : ∀ {Γ Δ A B} → (Γ ⊢ A) ≡ (Δ ⊢ B) → Γ ≡ Δ × A ≡ B
⊢-injective refl = refl , refl
