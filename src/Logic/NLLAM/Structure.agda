--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/NLIBC/Structure.agda
--------------------------------------------------------------------------------


open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLLAM.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.NLLAM.Type Atom as T hiding (module DecEq)


infixr 20 _∙_
data Structure : Set ℓ where
  ·_·  : Type      → Structure
  _∙_  : Structure → Structure → Structure
  I    : Structure
  B    : Structure
  C    : Structure


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.
··-injective : ∀ {p q} → · p · ≡ · q · → p ≡ q
··-injective refl = refl

∙-injective : ∀ {p₁ p₂ q₁ q₂} → p₁ ∙ q₁ ≡ p₂ ∙ q₂ → p₁ ≡ p₂ × q₁ ≡ q₂
∙-injective refl = refl , refl


-- Proof that if the given universe has decidable equality, then so do types.
module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where

  open T.DecEq _≟-Atom_ using (_≟-Type_)

  infix 4 _≟-Structure_

  _≟-Structure_ : (p q : Structure) → Dec (p ≡ q)
  · p ·   ≟-Structure · q ·   with p ≟-Type q
  ... | yes p=q rewrite p=q = yes refl
  ... | no  p≠q = no (λ x → p≠q (··-injective x))
  · p ·   ≟-Structure q₁ ∙ q₂ = no (λ ())
  · p ·   ≟-Structure I       = no (λ ())
  · p ·   ≟-Structure B       = no (λ ())
  · p ·   ≟-Structure C       = no (λ ())
  p₁ ∙ p₂ ≟-Structure · x ·   = no (λ ())
  p₁ ∙ p₂ ≟-Structure q₁ ∙ q₂ with p₁ ≟-Structure q₁ | p₂ ≟-Structure q₂
  ... | yes p₁=q₁ | yes p₂=q₂ rewrite p₁=q₁ | p₂=q₂ = yes refl
  ... | no  p₁≠q₁ | _         = no (λ x → p₁≠q₁ (proj₁ (∙-injective x)))
  ... | _         | no  p₂≠q₂ = no (λ x → p₂≠q₂ (proj₂ (∙-injective x)))
  p₁ ∙ p₂ ≟-Structure I       = no (λ ())
  p₁ ∙ p₂ ≟-Structure B       = no (λ ())
  p₁ ∙ p₂ ≟-Structure C       = no (λ ())
  I       ≟-Structure · q ·   = no (λ ())
  I       ≟-Structure q₁ ∙ q₂ = no (λ ())
  I       ≟-Structure I       = yes refl
  I       ≟-Structure B       = no (λ ())
  I       ≟-Structure C       = no (λ ())
  B       ≟-Structure · q ·   = no (λ ())
  B       ≟-Structure q₁ ∙ q₂ = no (λ ())
  B       ≟-Structure I       = no (λ ())
  B       ≟-Structure B       = yes refl
  B       ≟-Structure C       = no (λ ())
  C       ≟-Structure · q ·   = no (λ ())
  C       ≟-Structure q₁ ∙ q₂ = no (λ ())
  C       ≟-Structure I       = no (λ ())
  C       ≟-Structure B       = no (λ ())
  C       ≟-Structure C       = yes refl

  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Structure_
