--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------

open import Level                                      using (zero)
open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.NLP.SC.Type {ℓ} (Atom : Set ℓ) where


infixr 10 _&_
infixr 20 _⇒_
infixl 20 _⇐_
infixr 40 □_
infixr 40 ◇_
infixr 40 ■_
infixr 40 ◆_
infixr 40 □′_
infixr 40 ◇′_
infixr 40 ■′_
infixr 40 ◆′_


data Type : Set ℓ where

  el  : Atom → Type

  -- scope islands
  ⟨⟩_ : Type → Type

  -- infixation
  □_  : Type → Type
  ◇_  : Type → Type

  -- extraction
  ■_  : Type → Type
  ◆_  : Type → Type

  -- quantifier raising
  □′_ : Type → Type
  ◇′_ : Type → Type
  ■′_ : Type → Type
  ◆′_ : Type → Type

  -- choice
  _&_ : Type → Type → Type

  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type


-- Symmetries that should hold for these types.
infixl 10 _⋈ᵗ

_⋈ᵗ : Type → Type
(el  A) ⋈ᵗ = el A
(□   A) ⋈ᵗ = □  (A ⋈ᵗ)
(◇   A) ⋈ᵗ = ◇  (A ⋈ᵗ)
(■   A) ⋈ᵗ = ■  (A ⋈ᵗ)
(◆   A) ⋈ᵗ = ◆  (A ⋈ᵗ)
(□′  A) ⋈ᵗ = □′ (A ⋈ᵗ)
(◇′  A) ⋈ᵗ = ◇′ (A ⋈ᵗ)
(■′  A) ⋈ᵗ = ■′ (A ⋈ᵗ)
(◆′  A) ⋈ᵗ = ◆′ (A ⋈ᵗ)
(⟨⟩  A) ⋈ᵗ = ⟨⟩ (A ⋈ᵗ)
(A & B) ⋈ᵗ = (A ⋈ᵗ) & (B ⋈ᵗ)
(A ⇒ B) ⋈ᵗ = (B ⋈ᵗ) ⇐ (A ⋈ᵗ)
(B ⇐ A) ⋈ᵗ = (A ⋈ᵗ) ⇒ (B ⋈ᵗ)


open import Algebra.FunctionProperties {A = Type} _≡_


⋈ᵗ-inv : Involutive _⋈ᵗ
⋈ᵗ-inv (el  A)                             = refl
⋈ᵗ-inv (□   A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (◇   A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (■   A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (◆   A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (□′  A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (◇′  A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (■′  A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (◆′  A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (⟨⟩  A) rewrite ⋈ᵗ-inv A            = refl
⋈ᵗ-inv (A & B) rewrite ⋈ᵗ-inv A | ⋈ᵗ-inv B = refl
⋈ᵗ-inv (A ⇒ B) rewrite ⋈ᵗ-inv A | ⋈ᵗ-inv B = refl
⋈ᵗ-inv (B ⇐ A) rewrite ⋈ᵗ-inv A | ⋈ᵗ-inv B = refl



-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.
el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl

□-injective : ∀ {A B} → □ A ≡ □ B → A ≡ B
□-injective refl = refl

◇-injective : ∀ {A B} → ◇ A ≡ ◇ B → A ≡ B
◇-injective refl = refl

■-injective : ∀ {A B} → ■ A ≡ ■ B → A ≡ B
■-injective refl = refl

◆-injective : ∀ {A B} → ◆ A ≡ ◆ B → A ≡ B
◆-injective refl = refl

□′-injective : ∀ {A B} → □′ A ≡ □′ B → A ≡ B
□′-injective refl = refl

◇′-injective : ∀ {A B} → ◇′ A ≡ ◇′ B → A ≡ B
◇′-injective refl = refl

■′-injective : ∀ {A B} → ■′ A ≡ ■′ B → A ≡ B
■′-injective refl = refl

◆′-injective : ∀ {A B} → ◆′ A ≡ ◆′ B → A ≡ B
◆′-injective refl = refl

⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
⇒-injective refl = refl , refl

⇐-injective : ∀ {A B C D} → A ⇐ C ≡ B ⇐ D → A ≡ B × C ≡ D
⇐-injective refl = refl , refl

&-injective : ∀ {A B C D} → A & C ≡ B & D → A ≡ B × C ≡ D
&-injective refl = refl , refl
