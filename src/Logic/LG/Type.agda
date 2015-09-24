------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level                                      using (zero)
open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.LG.Type {ℓ} (Atom : Set ℓ) where


infixl 10 _⋈
infixl 10 _∞
infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇚_
infixr 25 _⇛_
infixr 30 _⊗_
infixr 30 _⊕_
infixr 40 □_
infixr 40 ◇_
infixr 40 ₀_
infixl 40 _⁰
infixr 40 ₁_
infixl 40 _¹


data Type : Set ℓ where

  el  : (A   : Atom) → Type
  □_  : (A   : Type) → Type
  ◇_  : (A   : Type) → Type
  ₀_  : (A   : Type) → Type
  _⁰  : (A   : Type) → Type
  ₁_  : (A   : Type) → Type
  _¹  : (A   : Type) → Type
  _⊗_ : (A B : Type) → Type
  _⇒_ : (A B : Type) → Type
  _⇐_ : (B A : Type) → Type
  _⊕_ : (B A : Type) → Type
  _⇚_ : (A A : Type) → Type
  _⇛_ : (B A : Type) → Type



-- Symmetries that should hold for these types.


_⋈ : Type → Type
(el  A) ⋈ = el       A
(□   A) ⋈ = □       (A ⋈)
(◇   A) ⋈ = ◇       (A ⋈)
(₀   A) ⋈ = (A ⋈)   ⁰
(A   ⁰) ⋈ = ₀       (A ⋈)
(₁   A) ⋈ = (A ⋈)   ¹
(A   ¹) ⋈ = ₁       (A ⋈)
(A ⊗ B) ⋈ = (B ⋈) ⊗ (A ⋈)
(A ⇒ B) ⋈ = (B ⋈) ⇐ (A ⋈)
(B ⇐ A) ⋈ = (A ⋈) ⇒ (B ⋈)
(B ⊕ A) ⋈ = (A ⋈) ⊕ (B ⋈)
(B ⇚ A) ⋈ = (A ⋈) ⇛ (B ⋈)
(A ⇛ B) ⋈ = (B ⋈) ⇚ (A ⋈)


_∞ : Type → Type
(el  A) ∞ = el       A
(□   A) ∞ = ◇       (A ∞)
(◇   A) ∞ = □       (A ∞)
(₀   A) ∞ = (A ∞)   ¹
(A   ⁰) ∞ = ₁       (A ∞)
(₁   A) ∞ = (A ∞)   ⁰
(A   ¹) ∞ = ₀       (A ∞)
(A ⊗ B) ∞ = (B ∞) ⊕ (A ∞)
(A ⇒ B) ∞ = (B ∞) ⇚ (A ∞)
(B ⇐ A) ∞ = (A ∞) ⇛ (B ∞)
(B ⊕ A) ∞ = (A ∞) ⊗ (B ∞)
(B ⇚ A) ∞ = (A ∞) ⇒ (B ∞)
(A ⇛ B) ∞ = (B ∞) ⇐ (A ∞)


open import Algebra.FunctionProperties {A = Type} _≡_


⋈-inv : Involutive _⋈
⋈-inv (el  A)                           = refl
⋈-inv (□   A) rewrite ⋈-inv A           = refl
⋈-inv (◇   A) rewrite ⋈-inv A           = refl
⋈-inv (₀   A) rewrite ⋈-inv A           = refl
⋈-inv (A   ⁰) rewrite ⋈-inv A           = refl
⋈-inv (₁   A) rewrite ⋈-inv A           = refl
⋈-inv (A   ¹) rewrite ⋈-inv A           = refl
⋈-inv (A ⊗ B) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (A ⇒ B) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (B ⇐ A) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (A ⊕ B) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (B ⇚ A) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (A ⇛ B) rewrite ⋈-inv A | ⋈-inv B = refl


∞-inv : Involutive _∞
∞-inv (el  A)                           = refl
∞-inv (□   A) rewrite ∞-inv A           = refl
∞-inv (◇   A) rewrite ∞-inv A           = refl
∞-inv (₀   A) rewrite ∞-inv A           = refl
∞-inv (A   ⁰) rewrite ∞-inv A           = refl
∞-inv (₁   A) rewrite ∞-inv A           = refl
∞-inv (A   ¹) rewrite ∞-inv A           = refl
∞-inv (A ⊗ B) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (A ⇒ B) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (B ⇐ A) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (A ⊕ B) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (B ⇚ A) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (A ⇛ B) rewrite ∞-inv A | ∞-inv B = refl


⋈∞⋈=∞ : (A : Type) → A ⋈ ∞ ⋈ ≡ A ∞
⋈∞⋈=∞ (el  A)                           = refl
⋈∞⋈=∞ (□   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (◇   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (₀   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (A   ⁰) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (₁   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (A   ¹) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (A ⊗ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (A ⇒ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (B ⇐ A) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (A ⊕ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (B ⇚ A) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (A ⇛ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl


∞⋈∞=⋈ : (A : Type) → A ∞ ⋈ ∞ ≡ A ⋈
∞⋈∞=⋈ (el  A)                           = refl
∞⋈∞=⋈ (□   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (◇   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (₀   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (A   ⁰) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (₁   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (A   ¹) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (A ⊗ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (A ⇒ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (B ⇐ A) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (A ⊕ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (B ⇚ A) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (A ⇛ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl


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
module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where

  infix 4 _≟-Type_

  _≟-Type_ : (A B : Type) → Dec (A ≡ B)
  el A  ≟-Type el C with (A ≟-Atom C)
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
