--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Type.agda
--------------------------------------------------------------------------------

open import Level                                      using (zero)
open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.MM96.Type {ℓ} (Atom : Set ℓ) where


infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇦_
infixr 25 _⇨_
infixr 30 _⊗_
infixr 30 _⊙_
infixr 40 ⟨l⟩_ ⟨r⟩_ □_ ◇_
data Type : Set ℓ where

  el   : Atom → Type
  ⟨t⟩  : Type
  ⟨l⟩_ : Type → Type
  ⟨r⟩_ : Type → Type
  ◇_   : Type → Type
  □_   : Type → Type
  _⊗_  : Type → Type → Type
  _⇒_  : Type → Type → Type
  _⇐_  : Type → Type → Type
  _⊙_  : Type → Type → Type
  _⇦_  : Type → Type → Type
  _⇨_  : Type → Type → Type



-- Symmetries that should hold for these types.


open import Algebra.FunctionProperties {A = Type} _≡_






-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.
el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl

⟨l⟩-injective : ∀ {A B} → ⟨l⟩ A ≡ ⟨l⟩ B → A ≡ B
⟨l⟩-injective refl = refl

⟨r⟩-injective : ∀ {A B} → ⟨r⟩ A ≡ ⟨r⟩ B → A ≡ B
⟨r⟩-injective refl = refl

◇-injective : ∀ {A B} → ◇ A ≡ ◇ B → A ≡ B
◇-injective refl = refl

□-injective : ∀ {A B} → □ A ≡ □ B → A ≡ B
□-injective refl = refl

⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
⇒-injective refl = refl , refl

⇐-injective : ∀ {A B C D} → A ⇐ C ≡ B ⇐ D → A ≡ B × C ≡ D
⇐-injective refl = refl , refl

⇦-injective : ∀ {A B C D} → A ⇦ C ≡ B ⇦ D → A ≡ B × C ≡ D
⇦-injective refl = refl , refl

⇨-injective : ∀ {A B C D} → A ⇨ C ≡ B ⇨ D → A ≡ B × C ≡ D
⇨-injective refl = refl , refl

⊗-injective : ∀ {A B C D} → A ⊗ C ≡ B ⊗ D → A ≡ B × C ≡ D
⊗-injective refl = refl , refl

⊙-injective : ∀ {A B C D} → A ⊙ C ≡ B ⊙ D → A ≡ B × C ≡ D
⊙-injective refl = refl , refl


-- Selective case matching
case-el : (A : Type) → Dec (∃ (λ U → A ≡ el U))
case-el (el  _) = yes (_ , refl)
case-el (⟨t⟩    ) = no (λ {(_ , ())})
case-el (◇   _) = no (λ {(_ , ())})
case-el (□   _) = no (λ {(_ , ())})
case-el (⟨l⟩ _) = no (λ {(_ , ())})
case-el (⟨r⟩ _) = no (λ {(_ , ())})
case-el (_ ⇒ _) = no (λ {(_ , ())})
case-el (_ ⇐ _) = no (λ {(_ , ())})
case-el (_ ⇦ _) = no (λ {(_ , ())})
case-el (_ ⇨ _) = no (λ {(_ , ())})
case-el (_ ⊗ _) = no (λ {(_ , ())})
case-el (_ ⊙ _) = no (λ {(_ , ())})

case-⟨l⟩ : (A : Type) → Dec (∃ (λ B → A ≡ ⟨l⟩ B))
case-⟨l⟩ (el  _) = no (λ {(_ , ())})
case-⟨l⟩ (⟨t⟩    ) = no (λ {(_ , ())})
case-⟨l⟩ (⟨l⟩ _) = yes (_ , refl)
case-⟨l⟩ (⟨r⟩ _) = no (λ {(_ , ())})
case-⟨l⟩ (◇   _) = no (λ {(_ , ())})
case-⟨l⟩ (□   _) = no (λ {(_ , ())})
case-⟨l⟩ (_ ⇒ _) = no (λ {(_ , ())})
case-⟨l⟩ (_ ⇐ _) = no (λ {(_ , ())})
case-⟨l⟩ (_ ⇦ _) = no (λ {(_ , ())})
case-⟨l⟩ (_ ⇨ _) = no (λ {(_ , ())})
case-⟨l⟩ (_ ⊗ _) = no (λ {(_ , ())})
case-⟨l⟩ (_ ⊙ _) = no (λ {(_ , ())})

case-⟨r⟩ : (A : Type) → Dec (∃ (λ B → A ≡ ⟨r⟩ B))
case-⟨r⟩ (el  _) = no (λ {(_ , ())})
case-⟨r⟩ (⟨t⟩    ) = no (λ {(_ , ())})
case-⟨r⟩ (⟨l⟩ _) = no (λ {(_ , ())})
case-⟨r⟩ (⟨r⟩ _) = yes (_ , refl)
case-⟨r⟩ (◇   _) = no (λ {(_ , ())})
case-⟨r⟩ (□   _) = no (λ {(_ , ())})
case-⟨r⟩ (_ ⇒ _) = no (λ {(_ , ())})
case-⟨r⟩ (_ ⇐ _) = no (λ {(_ , ())})
case-⟨r⟩ (_ ⇦ _) = no (λ {(_ , ())})
case-⟨r⟩ (_ ⇨ _) = no (λ {(_ , ())})
case-⟨r⟩ (_ ⊗ _) = no (λ {(_ , ())})
case-⟨r⟩ (_ ⊙ _) = no (λ {(_ , ())})

case-⇒ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇒ C))
case-⇒ (el  _) = no (λ {(_ , _ , ())})
case-⇒ (⟨t⟩    ) = no (λ {(_ , _ , ())})
case-⇒ (⟨l⟩ _) = no (λ {(_ , _ , ())})
case-⇒ (⟨r⟩ _) = no (λ {(_ , _ , ())})
case-⇒ (◇   _) = no (λ {(_ , _ , ())})
case-⇒ (□   _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⇒ _) = yes (_ , _ , refl)
case-⇒ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⇦ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⇨ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⊙ _) = no (λ {(_ , _ , ())})

case-⇐ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇐ C))
case-⇐ (el  _) = no (λ {(_ , _ , ())})
case-⇐ (⟨t⟩    ) = no (λ {(_ , _ , ())})
case-⇐ (⟨l⟩ _) = no (λ {(_ , _ , ())})
case-⇐ (⟨r⟩ _) = no (λ {(_ , _ , ())})
case-⇐ (◇   _) = no (λ {(_ , _ , ())})
case-⇐ (□   _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⇐ _) = yes (_ , _ , refl)
case-⇐ (_ ⇦ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⇨ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⊙ _) = no (λ {(_ , _ , ())})

case-⇨ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇨ C))
case-⇨ (el  _) = no (λ {(_ , _ , ())})
case-⇨ (⟨t⟩    ) = no (λ {(_ , _ , ())})
case-⇨ (⟨l⟩ _) = no (λ {(_ , _ , ())})
case-⇨ (⟨r⟩ _) = no (λ {(_ , _ , ())})
case-⇨ (◇   _) = no (λ {(_ , _ , ())})
case-⇨ (□   _) = no (λ {(_ , _ , ())})
case-⇨ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⇨ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⇨ (_ ⇦ _) = no (λ {(_ , _ , ())})
case-⇨ (_ ⇨ _) = yes (_ , _ , refl)
case-⇨ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇨ (_ ⊙ _) = no (λ {(_ , _ , ())})

case-⇦ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇦ C))
case-⇦ (el  _) = no (λ {(_ , _ , ())})
case-⇦ (⟨t⟩    ) = no (λ {(_ , _ , ())})
case-⇦ (⟨l⟩ _) = no (λ {(_ , _ , ())})
case-⇦ (⟨r⟩ _) = no (λ {(_ , _ , ())})
case-⇦ (◇   _) = no (λ {(_ , _ , ())})
case-⇦ (□   _) = no (λ {(_ , _ , ())})
case-⇦ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⇦ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⇦ (_ ⇦ _) = yes (_ , _ , refl)
case-⇦ (_ ⇨ _) = no (λ {(_ , _ , ())})
case-⇦ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇦ (_ ⊙ _) = no (λ {(_ , _ , ())})

case-⊗ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⊗ C))
case-⊗ (el  _) = no (λ {(_ , _ , ())})
case-⊗ (⟨t⟩    ) = no (λ {(_ , _ , ())})
case-⊗ (⟨l⟩ _) = no (λ {(_ , _ , ())})
case-⊗ (⟨r⟩ _) = no (λ {(_ , _ , ())})
case-⊗ (◇   _) = no (λ {(_ , _ , ())})
case-⊗ (□   _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇦ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇨ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⊗ _) = yes (_ , _ , refl)
case-⊗ (_ ⊙ _) = no (λ {(_ , _ , ())})

case-⊙ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⊙ C))
case-⊙ (el  _) = no (λ {(_ , _ , ())})
case-⊙ (⟨t⟩    ) = no (λ {(_ , _ , ())})
case-⊙ (⟨l⟩ _) = no (λ {(_ , _ , ())})
case-⊙ (⟨r⟩ _) = no (λ {(_ , _ , ())})
case-⊙ (◇   _) = no (λ {(_ , _ , ())})
case-⊙ (□   _) = no (λ {(_ , _ , ())})
case-⊙ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⊙ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⊙ (_ ⇦ _) = no (λ {(_ , _ , ())})
case-⊙ (_ ⇨ _) = no (λ {(_ , _ , ())})
case-⊙ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⊙ (_ ⊙ _) = yes (_ , _ , refl)


-- Proof that if the given universe has decidable equality, then so do types.
module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where

  infix 4 _≟-Type_

  _≟-Type_ : (A B : Type) → Dec (A ≡ B)
  el A  ≟-Type el  C with (A ≟-Atom C)
  ... | yes A=C rewrite A=C = yes refl
  ... | no  A≠C = no (A≠C ∘ el-injective)
  el  _ ≟-Type ⟨t⟩     = no (λ ())
  el A  ≟-Type ⟨l⟩ B = no (λ ())
  el A  ≟-Type ⟨r⟩ B = no (λ ())
  el A  ≟-Type ◇   B = no (λ ())
  el A  ≟-Type □   B = no (λ ())
  el A  ≟-Type C ⊗ D = no (λ ())
  el A  ≟-Type C ⇦ D = no (λ ())
  el A  ≟-Type C ⇨ D = no (λ ())
  el A  ≟-Type C ⊙ D = no (λ ())
  el A  ≟-Type C ⇐ D = no (λ ())
  el A  ≟-Type C ⇒ D = no (λ ())

  ⟨t⟩ ≟-Type el  _ = no (λ ())
  ⟨t⟩ ≟-Type ⟨t⟩     = yes refl
  ⟨t⟩ ≟-Type ⟨l⟩ _ = no (λ ())
  ⟨t⟩ ≟-Type ⟨r⟩ _ = no (λ ())
  ⟨t⟩ ≟-Type ◇   _ = no (λ ())
  ⟨t⟩ ≟-Type □   _ = no (λ ())
  ⟨t⟩ ≟-Type _ ⊗ _ = no (λ ())
  ⟨t⟩ ≟-Type _ ⇒ _ = no (λ ())
  ⟨t⟩ ≟-Type _ ⇐ _ = no (λ ())
  ⟨t⟩ ≟-Type _ ⊙ _ = no (λ ())
  ⟨t⟩ ≟-Type _ ⇦ _ = no (λ ())
  ⟨t⟩ ≟-Type _ ⇨ _ = no (λ ())

  ⟨l⟩ A   ≟-Type el  B = no (λ ())
  ⟨l⟩ _   ≟-Type ⟨t⟩     = no (λ ())
  ⟨l⟩ A   ≟-Type ⟨l⟩ B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ⟨l⟩-injective)
  ⟨l⟩ A   ≟-Type ⟨r⟩ B = no (λ ())
  ⟨l⟩ A   ≟-Type ◇   B = no (λ ())
  ⟨l⟩ A   ≟-Type □   B = no (λ ())
  ⟨l⟩ A   ≟-Type B ⇒ C = no (λ ())
  ⟨l⟩ A   ≟-Type B ⇐ C = no (λ ())
  ⟨l⟩ A   ≟-Type B ⇦ C = no (λ ())
  ⟨l⟩ A   ≟-Type B ⇨ C = no (λ ())
  ⟨l⟩ A   ≟-Type B ⊗ C = no (λ ())
  ⟨l⟩ A   ≟-Type B ⊙ C = no (λ ())

  ⟨r⟩ A   ≟-Type el  B = no (λ ())
  ⟨r⟩ _   ≟-Type ⟨t⟩     = no (λ ())
  ⟨r⟩ A   ≟-Type ⟨l⟩ B = no (λ ())
  ⟨r⟩ A   ≟-Type ⟨r⟩ B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ⟨r⟩-injective)
  ⟨r⟩ A   ≟-Type ◇   B = no (λ ())
  ⟨r⟩ A   ≟-Type □   B = no (λ ())
  ⟨r⟩ A   ≟-Type B ⇒ C = no (λ ())
  ⟨r⟩ A   ≟-Type B ⇐ C = no (λ ())
  ⟨r⟩ A   ≟-Type B ⇦ C = no (λ ())
  ⟨r⟩ A   ≟-Type B ⇨ C = no (λ ())
  ⟨r⟩ A   ≟-Type B ⊗ C = no (λ ())
  ⟨r⟩ A   ≟-Type B ⊙ C = no (λ ())

  ◇ A   ≟-Type el  B = no (λ ())
  ◇   _ ≟-Type ⟨t⟩     = no (λ ())
  ◇ A   ≟-Type ⟨l⟩ B = no (λ ())
  ◇ A   ≟-Type ⟨r⟩ B = no (λ ())
  ◇ A   ≟-Type ◇   B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ◇-injective)
  ◇ A   ≟-Type □   B = no (λ ())
  ◇ A   ≟-Type B ⇒ C = no (λ ())
  ◇ A   ≟-Type B ⇐ C = no (λ ())
  ◇ A   ≟-Type B ⇦ C = no (λ ())
  ◇ A   ≟-Type B ⇨ C = no (λ ())
  ◇ A   ≟-Type B ⊗ C = no (λ ())
  ◇ A   ≟-Type B ⊙ C = no (λ ())

  □ A   ≟-Type el  B = no (λ ())
  □   _ ≟-Type ⟨t⟩     = no (λ ())
  □ A   ≟-Type ⟨l⟩ B = no (λ ())
  □ A   ≟-Type ⟨r⟩ B = no (λ ())
  □ A   ≟-Type ◇   B = no (λ ())
  □ A   ≟-Type □   B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ □-injective)
  □ A   ≟-Type B ⇒ C = no (λ ())
  □ A   ≟-Type B ⇐ C = no (λ ())
  □ A   ≟-Type B ⇦ C = no (λ ())
  □ A   ≟-Type B ⇨ C = no (λ ())
  □ A   ≟-Type B ⊗ C = no (λ ())
  □ A   ≟-Type B ⊙ C = no (λ ())

  A ⊗ B ≟-Type el  C = no (λ ())
  _ ⊗ _ ≟-Type ⟨t⟩     = no (λ ())
  A ⊗ B ≟-Type ⟨l⟩ C = no (λ ())
  A ⊗ B ≟-Type ⟨r⟩ C = no (λ ())
  A ⊗ B ≟-Type ◇   C = no (λ ())
  A ⊗ B ≟-Type □   C = no (λ ())
  A ⊗ B ≟-Type C ⊗ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _                         = no (A≠C ∘ proj₁ ∘ ⊗-injective)
  ... | _       | no  B≠D                   = no (B≠D ∘ proj₂ ∘ ⊗-injective)
  A ⊗ B ≟-Type C ⇦ D = no (λ ())
  A ⊗ B ≟-Type C ⇨ D = no (λ ())
  A ⊗ B ≟-Type C ⊙ D = no (λ ())
  A ⊗ B ≟-Type C ⇐ D = no (λ ())
  A ⊗ B ≟-Type C ⇒ D = no (λ ())

  A ⇦ B ≟-Type el  C = no (λ ())
  _ ⇦ _ ≟-Type ⟨t⟩     = no (λ ())
  A ⇦ B ≟-Type ⟨l⟩ C = no (λ ())
  A ⇦ B ≟-Type ⟨r⟩ C = no (λ ())
  A ⇦ B ≟-Type ◇   C = no (λ ())
  A ⇦ B ≟-Type □   C = no (λ ())
  A ⇦ B ≟-Type C ⊗ D = no (λ ())
  A ⇦ B ≟-Type C ⇦ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇦-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇦-injective)
  A ⇦ B ≟-Type C ⇨ D = no (λ ())
  A ⇦ B ≟-Type C ⊙ D = no (λ ())
  A ⇦ B ≟-Type C ⇐ D = no (λ ())
  A ⇦ B ≟-Type C ⇒ D = no (λ ())

  A ⇨ B ≟-Type el  C = no (λ ())
  _ ⇨ _ ≟-Type ⟨t⟩     = no (λ ())
  A ⇨ B ≟-Type ⟨l⟩ C = no (λ ())
  A ⇨ B ≟-Type ⟨r⟩ C = no (λ ())
  A ⇨ B ≟-Type ◇   C = no (λ ())
  A ⇨ B ≟-Type □   C = no (λ ())
  A ⇨ B ≟-Type C ⊗ D = no (λ ())
  A ⇨ B ≟-Type C ⇦ D = no (λ ())
  A ⇨ B ≟-Type C ⇨ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇨-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇨-injective)
  A ⇨ B ≟-Type C ⊙ D = no (λ ())
  A ⇨ B ≟-Type C ⇐ D = no (λ ())
  A ⇨ B ≟-Type C ⇒ D = no (λ ())

  A ⊙ B ≟-Type el  C = no (λ ())
  _ ⊙ _ ≟-Type ⟨t⟩     = no (λ ())
  A ⊙ B ≟-Type ⟨l⟩ C = no (λ ())
  A ⊙ B ≟-Type ⟨r⟩ C = no (λ ())
  A ⊙ B ≟-Type ◇   C = no (λ ())
  A ⊙ B ≟-Type □   C = no (λ ())
  A ⊙ B ≟-Type C ⊗ D = no (λ ())
  A ⊙ B ≟-Type C ⇦ D = no (λ ())
  A ⊙ B ≟-Type C ⇨ D = no (λ ())
  A ⊙ B ≟-Type C ⊙ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⊙-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⊙-injective)
  A ⊙ B ≟-Type C ⇐ D = no (λ ())
  A ⊙ B ≟-Type C ⇒ D = no (λ ())

  A ⇐ B ≟-Type el  C = no (λ ())
  _ ⇐ _ ≟-Type ⟨t⟩     = no (λ ())
  A ⇐ B ≟-Type ⟨l⟩ C = no (λ ())
  A ⇐ B ≟-Type ⟨r⟩ C = no (λ ())
  A ⇐ B ≟-Type ◇   C = no (λ ())
  A ⇐ B ≟-Type □   C = no (λ ())
  A ⇐ B ≟-Type C ⊗ D = no (λ ())
  A ⇐ B ≟-Type C ⇦ D = no (λ ())
  A ⇐ B ≟-Type C ⇨ D = no (λ ())
  A ⇐ B ≟-Type C ⊙ D = no (λ ())
  A ⇐ B ≟-Type C ⇐ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇐-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇐-injective)
  A ⇐ B ≟-Type C ⇒ D = no (λ ())

  A ⇒ B ≟-Type el  C = no (λ ())
  _ ⇒ _ ≟-Type ⟨t⟩   = no (λ ())
  A ⇒ B ≟-Type ⟨l⟩ C = no (λ ())
  A ⇒ B ≟-Type ⟨r⟩ C = no (λ ())
  A ⇒ B ≟-Type ◇   C = no (λ ())
  A ⇒ B ≟-Type □   C = no (λ ())
  A ⇒ B ≟-Type C ⊗ D = no (λ ())
  A ⇒ B ≟-Type C ⇦ D = no (λ ())
  A ⇒ B ≟-Type C ⇨ D = no (λ ())
  A ⇒ B ≟-Type C ⊙ D = no (λ ())
  A ⇒ B ≟-Type C ⇐ D = no (λ ())
  A ⇒ B ≟-Type C ⇒ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇒-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇒-injective)


  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Type_
