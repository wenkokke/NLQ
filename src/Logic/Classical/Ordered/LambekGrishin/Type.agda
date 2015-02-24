------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.Classical.Ordered.LambekGrishin.Type {ℓ} (Univ : Set ℓ) where


infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇚_
infixr 25 _⇛_
infixr 30 _⊗_
infixr 30 _⊕_


data Type : Set ℓ where

  el  : Univ → Type

  □_  : Type → Type
  ◇_  : Type → Type

  ₀_  : Type → Type
  _⁰  : Type → Type
  ₁_  : Type → Type
  _¹  : Type → Type

  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type

  _⇚_ : Type → Type → Type
  _⇛_ : Type → Type → Type

  _⊗_ : Type → Type → Type
  _⊕_ : Type → Type → Type


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.

el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl

□-injective : ∀ {A B} → □ A ≡ □ B → A ≡ B
□-injective refl = refl

◇-injective : ∀ {A B} → ◇ A ≡ ◇ B → A ≡ B
◇-injective refl = refl

₀-injective : ∀ {A B} → ₀ A ≡ ₀ B → A ≡ B
₀-injective refl = refl

⁰-injective : ∀ {A B} → A ⁰ ≡ B ⁰ → A ≡ B
⁰-injective refl = refl

₁-injective : ∀ {A B} → ₁ A ≡ ₁ B → A ≡ B
₁-injective refl = refl

¹-injective : ∀ {A B} → A ¹ ≡ B ¹ → A ≡ B
¹-injective refl = refl

⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
⇒-injective refl = refl , refl

⇐-injective : ∀ {A B C D} → A ⇐ C ≡ B ⇐ D → A ≡ B × C ≡ D
⇐-injective refl = refl , refl

⇚-injective : ∀ {A B C D} → A ⇚ C ≡ B ⇚ D → A ≡ B × C ≡ D
⇚-injective refl = refl , refl

⇛-injective : ∀ {A B C D} → A ⇛ C ≡ B ⇛ D → A ≡ B × C ≡ D
⇛-injective refl = refl , refl

⊗-injective : ∀ {A B C D} → A ⊗ C ≡ B ⊗ D → A ≡ B × C ≡ D
⊗-injective refl = refl , refl

⊕-injective : ∀ {A B C D} → A ⊕ C ≡ B ⊕ D → A ≡ B × C ≡ D
⊕-injective refl = refl , refl


-- Selective case matching
case-el : (A : Type) → Dec (∃ (λ U → A ≡ el U))
case-el (el  _) = yes (_ , refl)
case-el (□   _) = no (λ {(_ , ())})
case-el (◇   _) = no (λ {(_ , ())})
case-el (₀   _) = no (λ {(_ , ())})
case-el (_   ⁰) = no (λ {(_ , ())})
case-el (₁   _) = no (λ {(_ , ())})
case-el (_   ¹) = no (λ {(_ , ())})
case-el (_ ⇒ _) = no (λ {(_ , ())})
case-el (_ ⇐ _) = no (λ {(_ , ())})
case-el (_ ⇚ _) = no (λ {(_ , ())})
case-el (_ ⇛ _) = no (λ {(_ , ())})
case-el (_ ⊗ _) = no (λ {(_ , ())})
case-el (_ ⊕ _) = no (λ {(_ , ())})

case-□ : (A : Type) → Dec (∃ (λ B → A ≡ □ B))
case-□ (el  _) = no (λ {(_ , ())})
case-□ (□   _) = yes (_ , refl)
case-□ (◇   _) = no (λ {(_ , ())})
case-□ (₀   _) = no (λ {(_ , ())})
case-□ (_   ⁰) = no (λ {(_ , ())})
case-□ (₁   _) = no (λ {(_ , ())})
case-□ (_   ¹) = no (λ {(_ , ())})
case-□ (_ ⇒ _) = no (λ {(_ , ())})
case-□ (_ ⇐ _) = no (λ {(_ , ())})
case-□ (_ ⇚ _) = no (λ {(_ , ())})
case-□ (_ ⇛ _) = no (λ {(_ , ())})
case-□ (_ ⊗ _) = no (λ {(_ , ())})
case-□ (_ ⊕ _) = no (λ {(_ , ())})

case-◇ : (A : Type) → Dec (∃ (λ B → A ≡ ◇ B))
case-◇ (el  _) = no (λ {(_ , ())})
case-◇ (□   _) = no (λ {(_ , ())})
case-◇ (◇   _) = yes (_ , refl)
case-◇ (₀   _) = no (λ {(_ , ())})
case-◇ (_   ⁰) = no (λ {(_ , ())})
case-◇ (₁   _) = no (λ {(_ , ())})
case-◇ (_   ¹) = no (λ {(_ , ())})
case-◇ (_ ⇒ _) = no (λ {(_ , ())})
case-◇ (_ ⇐ _) = no (λ {(_ , ())})
case-◇ (_ ⇚ _) = no (λ {(_ , ())})
case-◇ (_ ⇛ _) = no (λ {(_ , ())})
case-◇ (_ ⊗ _) = no (λ {(_ , ())})
case-◇ (_ ⊕ _) = no (λ {(_ , ())})

case-⇒ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇒ C))
case-⇒ (el  _) = no (λ {(_ , _ , ())})
case-⇒ (□   _) = no (λ {(_ , _ , ())})
case-⇒ (◇   _) = no (λ {(_ , _ , ())})
case-⇒ (₀   _) = no (λ {(_ , _ , ())})
case-⇒ (_   ⁰) = no (λ {(_ , _ , ())})
case-⇒ (₁   _) = no (λ {(_ , _ , ())})
case-⇒ (_   ¹) = no (λ {(_ , _ , ())})
case-⇒ (_ ⇒ _) = yes (_ , _ , refl)
case-⇒ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⇚ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⇛ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇒ (_ ⊕ _) = no (λ {(_ , _ , ())})

case-⇐ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇐ C))
case-⇐ (el  _) = no (λ {(_ , _ , ())})
case-⇐ (□   _) = no (λ {(_ , _ , ())})
case-⇐ (◇   _) = no (λ {(_ , _ , ())})
case-⇐ (₀   _) = no (λ {(_ , _ , ())})
case-⇐ (_   ⁰) = no (λ {(_ , _ , ())})
case-⇐ (₁   _) = no (λ {(_ , _ , ())})
case-⇐ (_   ¹) = no (λ {(_ , _ , ())})
case-⇐ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⇐ _) = yes (_ , _ , refl)
case-⇐ (_ ⇚ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⇛ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇐ (_ ⊕ _) = no (λ {(_ , _ , ())})

case-⇛ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇛ C))
case-⇛ (el  _) = no (λ {(_ , _ , ())})
case-⇛ (□   _) = no (λ {(_ , _ , ())})
case-⇛ (◇   _) = no (λ {(_ , _ , ())})
case-⇛ (₀   _) = no (λ {(_ , _ , ())})
case-⇛ (_   ⁰) = no (λ {(_ , _ , ())})
case-⇛ (₁   _) = no (λ {(_ , _ , ())})
case-⇛ (_   ¹) = no (λ {(_ , _ , ())})
case-⇛ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⇛ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⇛ (_ ⇚ _) = no (λ {(_ , _ , ())})
case-⇛ (_ ⇛ _) = yes (_ , _ , refl)
case-⇛ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇛ (_ ⊕ _) = no (λ {(_ , _ , ())})

case-⇚ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⇚ C))
case-⇚ (el  _) = no (λ {(_ , _ , ())})
case-⇚ (□   _) = no (λ {(_ , _ , ())})
case-⇚ (◇   _) = no (λ {(_ , _ , ())})
case-⇚ (₀   _) = no (λ {(_ , _ , ())})
case-⇚ (_   ⁰) = no (λ {(_ , _ , ())})
case-⇚ (₁   _) = no (λ {(_ , _ , ())})
case-⇚ (_   ¹) = no (λ {(_ , _ , ())})
case-⇚ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⇚ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⇚ (_ ⇚ _) = yes (_ , _ , refl)
case-⇚ (_ ⇛ _) = no (λ {(_ , _ , ())})
case-⇚ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⇚ (_ ⊕ _) = no (λ {(_ , _ , ())})

case-⊗ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⊗ C))
case-⊗ (el  _) = no (λ {(_ , _ , ())})
case-⊗ (□   _) = no (λ {(_ , _ , ())})
case-⊗ (◇   _) = no (λ {(_ , _ , ())})
case-⊗ (₀   _) = no (λ {(_ , _ , ())})
case-⊗ (_   ⁰) = no (λ {(_ , _ , ())})
case-⊗ (₁   _) = no (λ {(_ , _ , ())})
case-⊗ (_   ¹) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇚ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⇛ _) = no (λ {(_ , _ , ())})
case-⊗ (_ ⊗ _) = yes (_ , _ , refl)
case-⊗ (_ ⊕ _) = no (λ {(_ , _ , ())})

case-⊕ : (A : Type) → Dec (∃₂ (λ B C → A ≡ B ⊕ C))
case-⊕ (el  _) = no (λ {(_ , _ , ())})
case-⊕ (□   _) = no (λ {(_ , _ , ())})
case-⊕ (◇   _) = no (λ {(_ , _ , ())})
case-⊕ (₀   _) = no (λ {(_ , _ , ())})
case-⊕ (_   ⁰) = no (λ {(_ , _ , ())})
case-⊕ (₁   _) = no (λ {(_ , _ , ())})
case-⊕ (_   ¹) = no (λ {(_ , _ , ())})
case-⊕ (_ ⇒ _) = no (λ {(_ , _ , ())})
case-⊕ (_ ⇐ _) = no (λ {(_ , _ , ())})
case-⊕ (_ ⇚ _) = no (λ {(_ , _ , ())})
case-⊕ (_ ⇛ _) = no (λ {(_ , _ , ())})
case-⊕ (_ ⊗ _) = no (λ {(_ , _ , ())})
case-⊕ (_ ⊕ _) = yes (_ , _ , refl)


-- Proof that if the given universe has decidable equality, then so do types.
module DecEq
       (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B))
       where

  infix 4 _≟-Type_

  _≟-Type_ : (A B : Type) → Dec (A ≡ B)
  el A  ≟-Type el C with (A ≟-Univ C)
  ... | yes A=C rewrite A=C = yes refl
  ... | no  A≠C = no (A≠C ∘ el-injective)
  el A  ≟-Type □ B   = no (λ ())
  el A  ≟-Type ◇ B   = no (λ ())
  el A  ≟-Type ₀ B   = no (λ ())
  el A  ≟-Type B ⁰   = no (λ ())
  el A  ≟-Type ₁ B   = no (λ ())
  el A  ≟-Type B ¹   = no (λ ())
  el A  ≟-Type C ⊗ D = no (λ ())
  el A  ≟-Type C ⇚ D = no (λ ())
  el A  ≟-Type C ⇛ D = no (λ ())
  el A  ≟-Type C ⊕ D = no (λ ())
  el A  ≟-Type C ⇐ D = no (λ ())
  el A  ≟-Type C ⇒ D = no (λ ())

  □ A   ≟-Type el B  = no (λ ())
  □ A   ≟-Type □ B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ □-injective)
  □ A   ≟-Type ◇ B   = no (λ ())
  □ A   ≟-Type ₀ B   = no (λ ())
  □ A   ≟-Type B ⁰   = no (λ ())
  □ A   ≟-Type ₁ B   = no (λ ())
  □ A   ≟-Type B ¹   = no (λ ())
  □ A   ≟-Type B ⇒ C = no (λ ())
  □ A   ≟-Type B ⇐ C = no (λ ())
  □ A   ≟-Type B ⇚ C = no (λ ())
  □ A   ≟-Type B ⇛ C = no (λ ())
  □ A   ≟-Type B ⊗ C = no (λ ())
  □ A   ≟-Type B ⊕ C = no (λ ())

  ◇ A   ≟-Type el B  = no (λ ())
  ◇ A   ≟-Type □ B   = no (λ ())
  ◇ A   ≟-Type ◇ B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ◇-injective)
  ◇ A   ≟-Type ₀ B   = no (λ ())
  ◇ A   ≟-Type B ⁰   = no (λ ())
  ◇ A   ≟-Type ₁ B   = no (λ ())
  ◇ A   ≟-Type B ¹   = no (λ ())
  ◇ A   ≟-Type B ⇒ C = no (λ ())
  ◇ A   ≟-Type B ⇐ C = no (λ ())
  ◇ A   ≟-Type B ⇚ C = no (λ ())
  ◇ A   ≟-Type B ⇛ C = no (λ ())
  ◇ A   ≟-Type B ⊗ C = no (λ ())
  ◇ A   ≟-Type B ⊕ C = no (λ ())

  ₀ A   ≟-Type el B  = no (λ ())
  ₀ A   ≟-Type □ B   = no (λ ())
  ₀ A   ≟-Type ◇ B   = no (λ ())
  ₀ A   ≟-Type ₀ B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ₀-injective)
  ₀ A   ≟-Type B ⁰   = no (λ ())
  ₀ A   ≟-Type ₁ B   = no (λ ())
  ₀ A   ≟-Type B ¹   = no (λ ())
  ₀ A   ≟-Type B ⇒ C = no (λ ())
  ₀ A   ≟-Type B ⇐ C = no (λ ())
  ₀ A   ≟-Type B ⇚ C = no (λ ())
  ₀ A   ≟-Type B ⇛ C = no (λ ())
  ₀ A   ≟-Type B ⊗ C = no (λ ())
  ₀ A   ≟-Type B ⊕ C = no (λ ())

  A ⁰   ≟-Type el B  = no (λ ())
  A ⁰   ≟-Type □ B   = no (λ ())
  A ⁰   ≟-Type ◇ B   = no (λ ())
  A ⁰   ≟-Type ₀ B   = no (λ ())
  A ⁰   ≟-Type B ⁰ with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ⁰-injective)
  A ⁰   ≟-Type ₁ B   = no (λ ())
  A ⁰   ≟-Type B ¹   = no (λ ())
  A ⁰   ≟-Type B ⇒ C = no (λ ())
  A ⁰   ≟-Type B ⇐ C = no (λ ())
  A ⁰   ≟-Type B ⇚ C = no (λ ())
  A ⁰   ≟-Type B ⇛ C = no (λ ())
  A ⁰   ≟-Type B ⊗ C = no (λ ())
  A ⁰   ≟-Type B ⊕ C = no (λ ())

  ₁ A   ≟-Type el B = no (λ ())
  ₁ A   ≟-Type □ B  = no (λ ())
  ₁ A   ≟-Type ◇ B  = no (λ ())
  ₁ A   ≟-Type ₀ B  = no (λ ())
  ₁ A   ≟-Type B ⁰  = no (λ ())
  ₁ A   ≟-Type ₁ B with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ₁-injective)
  ₁ A   ≟-Type B ¹  = no (λ ())
  ₁ A   ≟-Type B ⇒ C = no (λ ())
  ₁ A   ≟-Type B ⇐ C = no (λ ())
  ₁ A   ≟-Type B ⇚ C = no (λ ())
  ₁ A   ≟-Type B ⇛ C = no (λ ())
  ₁ A   ≟-Type B ⊗ C = no (λ ())
  ₁ A   ≟-Type B ⊕ C = no (λ ())

  A ¹   ≟-Type el B  = no (λ ())
  A ¹   ≟-Type □ B   = no (λ ())
  A ¹   ≟-Type ◇ B   = no (λ ())
  A ¹   ≟-Type ₀ B   = no (λ ())
  A ¹   ≟-Type B ⁰   = no (λ ())
  A ¹   ≟-Type ₁ B   = no (λ ())
  A ¹   ≟-Type B ¹ with A ≟-Type B
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ¹-injective)
  A ¹   ≟-Type B ⇒ C = no (λ ())
  A ¹   ≟-Type B ⇐ C = no (λ ())
  A ¹   ≟-Type B ⇚ C = no (λ ())
  A ¹   ≟-Type B ⇛ C = no (λ ())
  A ¹   ≟-Type B ⊗ C = no (λ ())
  A ¹   ≟-Type B ⊕ C = no (λ ())

  A ⊗ B ≟-Type el C  = no (λ ())
  A ⊗ B ≟-Type □ C   = no (λ ())
  A ⊗ B ≟-Type ◇ C   = no (λ ())
  A ⊗ B ≟-Type ₀ C   = no (λ ())
  A ⊗ B ≟-Type C ⁰   = no (λ ())
  A ⊗ B ≟-Type ₁ C   = no (λ ())
  A ⊗ B ≟-Type C ¹   = no (λ ())
  A ⊗ B ≟-Type C ⊗ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _                         = no (A≠C ∘ proj₁ ∘ ⊗-injective)
  ... | _       | no  B≠D                   = no (B≠D ∘ proj₂ ∘ ⊗-injective)
  A ⊗ B ≟-Type C ⇚ D = no (λ ())
  A ⊗ B ≟-Type C ⇛ D = no (λ ())
  A ⊗ B ≟-Type C ⊕ D = no (λ ())
  A ⊗ B ≟-Type C ⇐ D = no (λ ())
  A ⊗ B ≟-Type C ⇒ D = no (λ ())

  A ⇚ B ≟-Type el C  = no (λ ())
  A ⇚ B ≟-Type □ C   = no (λ ())
  A ⇚ B ≟-Type ◇ C   = no (λ ())
  A ⇚ B ≟-Type ₀ C   = no (λ ())
  A ⇚ B ≟-Type C ⁰   = no (λ ())
  A ⇚ B ≟-Type ₁ C   = no (λ ())
  A ⇚ B ≟-Type C ¹   = no (λ ())
  A ⇚ B ≟-Type C ⊗ D = no (λ ())
  A ⇚ B ≟-Type C ⇚ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇚-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇚-injective)
  A ⇚ B ≟-Type C ⇛ D = no (λ ())
  A ⇚ B ≟-Type C ⊕ D = no (λ ())
  A ⇚ B ≟-Type C ⇐ D = no (λ ())
  A ⇚ B ≟-Type C ⇒ D = no (λ ())

  A ⇛ B ≟-Type el C  = no (λ ())
  A ⇛ B ≟-Type □ C   = no (λ ())
  A ⇛ B ≟-Type ◇ C   = no (λ ())
  A ⇛ B ≟-Type ₀ C   = no (λ ())
  A ⇛ B ≟-Type C ⁰   = no (λ ())
  A ⇛ B ≟-Type ₁ C   = no (λ ())
  A ⇛ B ≟-Type C ¹   = no (λ ())
  A ⇛ B ≟-Type C ⊗ D = no (λ ())
  A ⇛ B ≟-Type C ⇚ D = no (λ ())
  A ⇛ B ≟-Type C ⇛ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇛-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇛-injective)
  A ⇛ B ≟-Type C ⊕ D = no (λ ())
  A ⇛ B ≟-Type C ⇐ D = no (λ ())
  A ⇛ B ≟-Type C ⇒ D = no (λ ())

  A ⊕ B ≟-Type el C  = no (λ ())
  A ⊕ B ≟-Type □ C   = no (λ ())
  A ⊕ B ≟-Type ◇ C   = no (λ ())
  A ⊕ B ≟-Type ₀ C   = no (λ ())
  A ⊕ B ≟-Type C ⁰   = no (λ ())
  A ⊕ B ≟-Type ₁ C   = no (λ ())
  A ⊕ B ≟-Type C ¹   = no (λ ())
  A ⊕ B ≟-Type C ⊗ D = no (λ ())
  A ⊕ B ≟-Type C ⇚ D = no (λ ())
  A ⊕ B ≟-Type C ⇛ D = no (λ ())
  A ⊕ B ≟-Type C ⊕ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⊕-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⊕-injective)
  A ⊕ B ≟-Type C ⇐ D = no (λ ())
  A ⊕ B ≟-Type C ⇒ D = no (λ ())

  A ⇐ B ≟-Type el C  = no (λ ())
  A ⇐ B ≟-Type □ C   = no (λ ())
  A ⇐ B ≟-Type ◇ C   = no (λ ())
  A ⇐ B ≟-Type ₀ C   = no (λ ())
  A ⇐ B ≟-Type C ⁰   = no (λ ())
  A ⇐ B ≟-Type ₁ C   = no (λ ())
  A ⇐ B ≟-Type C ¹   = no (λ ())
  A ⇐ B ≟-Type C ⊗ D = no (λ ())
  A ⇐ B ≟-Type C ⇚ D = no (λ ())
  A ⇐ B ≟-Type C ⇛ D = no (λ ())
  A ⇐ B ≟-Type C ⊕ D = no (λ ())
  A ⇐ B ≟-Type C ⇐ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇐-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇐-injective)
  A ⇐ B ≟-Type C ⇒ D = no (λ ())

  A ⇒ B ≟-Type el C  = no (λ ())
  A ⇒ B ≟-Type □ C   = no (λ ())
  A ⇒ B ≟-Type ◇ C   = no (λ ())
  A ⇒ B ≟-Type ₀ C   = no (λ ())
  A ⇒ B ≟-Type C ⁰   = no (λ ())
  A ⇒ B ≟-Type ₁ C   = no (λ ())
  A ⇒ B ≟-Type C ¹   = no (λ ())
  A ⇒ B ≟-Type C ⊗ D = no (λ ())
  A ⇒ B ≟-Type C ⇚ D = no (λ ())
  A ⇒ B ≟-Type C ⇛ D = no (λ ())
  A ⇒ B ≟-Type C ⊕ D = no (λ ())
  A ⇒ B ≟-Type C ⇐ D = no (λ ())
  A ⇒ B ≟-Type C ⇒ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A=C | yes B=D rewrite A=C | B=D = yes refl
  ... | no  A≠C | _       = no (A≠C ∘ proj₁ ∘ ⇒-injective)
  ... | _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⇒-injective)


  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Type_
