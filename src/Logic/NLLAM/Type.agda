--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/NLIBC/Type.agda
--------------------------------------------------------------------------------


open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLLAM.Type {ℓ} (Atom : Set ℓ) where


infixr 30 _⇒_ _⇨_
infixl 30 _⇐_ _⇦_


data Type : Set ℓ where

  el  : Atom → Type

  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type

  _⇨_ : Type → Type → Type
  _⇦_ : Type → Type → Type


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.
el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl

⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
⇒-injective refl = refl , refl

⇐-injective : ∀ {A B C D} → A ⇐ C ≡ B ⇐ D → A ≡ B × C ≡ D
⇐-injective refl = refl , refl

⇨-injective : ∀ {A B C D} → A ⇨ C ≡ B ⇨ D → A ≡ B × C ≡ D
⇨-injective refl = refl , refl

⇦-injective : ∀ {A B C D} → A ⇦ C ≡ B ⇦ D → A ≡ B × C ≡ D
⇦-injective refl = refl , refl


-- Proof that if the given universe has decidable equality, then so do types.
module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where

  infix 4 _≟-Type_

  _≟-Type_ : (p q : Type) → Dec (p ≡ q)
  el p    ≟-Type el q    with p ≟-Atom q
  ... | yes p=q rewrite p=q = yes refl
  ... | no  p≠q = no (λ x → p≠q (el-injective x))
  el p    ≟-Type q₁ ⇒ q₂ = no (λ ())
  el p    ≟-Type q₁ ⇐ q₂ = no (λ ())
  el p    ≟-Type q₁ ⇨ q₂ = no (λ ())
  el p    ≟-Type q₁ ⇦ q₂ = no (λ ())
  p₁ ⇒ p₂ ≟-Type el x    = no (λ ())
  p₁ ⇒ p₂ ≟-Type q₁ ⇒ q₂ with p₁ ≟-Type q₁ | p₂ ≟-Type q₂
  ... | yes p₁=q₁ | yes p₂=q₂ rewrite p₁=q₁ | p₂=q₂ = yes refl
  ... | no  p₁≠q₁ | _         = no (λ x → p₁≠q₁ (proj₁ (⇒-injective x)))
  ... | _         | no  p₂≠q₂ = no (λ x → p₂≠q₂ (proj₂ (⇒-injective x)))
  p₁ ⇒ p₂ ≟-Type q₁ ⇐ q₂ = no (λ ())
  p₁ ⇒ p₂ ≟-Type q₁ ⇨ q₂ = no (λ ())
  p₁ ⇒ p₂ ≟-Type q₁ ⇦ q₂ = no (λ ())
  p₁ ⇐ p₂ ≟-Type el x    = no (λ ())
  p₁ ⇐ p₂ ≟-Type q₁ ⇒ q₂ = no (λ ())
  p₁ ⇐ p₂ ≟-Type q₁ ⇐ q₂ with p₁ ≟-Type q₁ | p₂ ≟-Type q₂
  ... | yes p₁=q₁ | yes p₂=q₂ rewrite p₁=q₁ | p₂=q₂ = yes refl
  ... | no  p₁≠q₁ | _         = no (λ x → p₁≠q₁ (proj₁ (⇐-injective x)))
  ... | _         | no  p₂≠q₂ = no (λ x → p₂≠q₂ (proj₂ (⇐-injective x)))
  p₁ ⇐ p₂ ≟-Type q₁ ⇨ q₂ = no (λ ())
  p₁ ⇐ p₂ ≟-Type q₁ ⇦ q₂ = no (λ ())
  p₁ ⇨ p₂ ≟-Type el x    = no (λ ())
  p₁ ⇨ p₂ ≟-Type q₁ ⇒ q₂ = no (λ ())
  p₁ ⇨ p₂ ≟-Type q₁ ⇐ q₂ = no (λ ())
  p₁ ⇨ p₂ ≟-Type q₁ ⇨ q₂ with p₁ ≟-Type q₁ | p₂ ≟-Type q₂
  ... | yes p₁=q₁ | yes p₂=q₂ rewrite p₁=q₁ | p₂=q₂ = yes refl
  ... | no  p₁≠q₁ | _         = no (λ x → p₁≠q₁ (proj₁ (⇨-injective x)))
  ... | _         | no  p₂≠q₂ = no (λ x → p₂≠q₂ (proj₂ (⇨-injective x)))
  p₁ ⇨ p₂ ≟-Type q₁ ⇦ q₂ = no (λ ())
  p₁ ⇦ p₂ ≟-Type el x    = no (λ ())
  p₁ ⇦ p₂ ≟-Type q₁ ⇒ q₂ = no (λ ())
  p₁ ⇦ p₂ ≟-Type q₁ ⇐ q₂ = no (λ ())
  p₁ ⇦ p₂ ≟-Type q₁ ⇨ q₂ = no (λ ())
  p₁ ⇦ p₂ ≟-Type q₁ ⇦ q₂ with p₁ ≟-Type q₁ | p₂ ≟-Type q₂
  ... | yes p₁=q₁ | yes p₂=q₂ rewrite p₁=q₁ | p₂=q₂ = yes refl
  ... | no  p₁≠q₁ | _         = no (λ x → p₁≠q₁ (proj₁ (⇦-injective x)))
  ... | _         | no  p₂≠q₂ = no (λ x → p₂≠q₂ (proj₂ (⇦-injective x)))

  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Type_
