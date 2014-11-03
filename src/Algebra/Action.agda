------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of actions of semigroups and monoids on setoids.
------------------------------------------------------------------------

module Algebra.Action where

open import Algebra.FunctionProperties as FunctionProperties using (Op₁; Op₂)
open import Algebra.Structures
open import Function
open import Level using (_⊔_)
open import Relation.Binary

------------------------------------------------------------------------
-- Semigroup actions and monoid actions


Action : ∀ {a b ℓ} {A : Set a} {B : Set b}
         → (≈ : Rel B ℓ) (∙ : Op₂ A) ($ : A → B → B)
         → Set (a ⊔ b ⊔ ℓ)
Action {A = A} {B = B} _≈_ _∙_ _$_
  = (f g : A) (x : B) → (f $ (g $ x)) ≈ ((f ∙ g) $ x)

ActionIdentity : ∀ {a b ℓ} {A : Set a} {B : Set b}
               → (≈ : Rel B ℓ) (ε : A) ($ : A → B → B)
               → Set (b ⊔ ℓ)
ActionIdentity {A = A} {B = B} _≈_ ε _$_
  = (x : B) → (ε $ x) ≈ x


record IsSemigroupAction {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
                         (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂)
                         (∙ : Op₂ A) ($ : A → B → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isSemigroup : IsSemigroup ≈₁ ∙
    action      : Action ≈₂ ∙ $

  open IsSemigroup isSemigroup public


record IsMonoidAction {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
                      (≈₁ : Rel A ℓ₁) (≈₂ : Rel B ℓ₂)
                      (∙ : Op₂ A) (ε : A) ($ : A → B → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where

  field
    isMonoid    : IsMonoid ≈₁ ∙ ε
    action      : Action ≈₂ ∙ $
    identityˡ   : ActionIdentity ≈₂ ε $

  open IsMonoid isMonoid public
