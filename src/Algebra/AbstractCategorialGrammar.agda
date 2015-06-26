------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

module Algebra.AbstractCategorialGrammar where


open import Data.Nat                              using (ℕ; suc; _⊔_)
open import Data.List                             using (List; _++_; map) renaming (_∷_ to _,_; [] to ∅)
open import Data.List.Properties                  using (map-++-commute)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


-- TODO:
--   This code has to be rewritten the instance issue 1570 gets fixed,
--   as it is in no way readable.
--


private
  module _ where
    module Internal-Type (Atom : Set) where

      infix  3 _⊢_
      infixr 5 _⊸_

      data Type : Set where
        el   : Atom  → Type
        _⊸_  : Type  → Type → Type

      data Judgement : Set where
        _⊢_ : (X : List Type) (A : Type) → Judgement

      -- compute the order of a type
      ordᵀ : Type → ℕ
      ordᵀ (el A) = 1
      ordᵀ (A ⊸ B) = suc (ordᵀ A) ⊔ ordᵀ B

  record Vocabulary : Set₁ where
    field
      Atom : Set
      Word : Set

    open Internal-Type Atom public

    field
      TypeOf : Word → Type

    infix  1 Expr_

    data Expr_ : Judgement → Set where

      var : ∀ {A}        → Expr  A , ∅ ⊢ A

      con : ∀ x
          → Expr  ∅ ⊢ TypeOf(x)

      abs : ∀ {X A B}    → Expr  A , X ⊢ B
          → Expr  X ⊢ A ⊸ B

      app : ∀ {X Y A B}  → Expr  X ⊢ A ⊸ B
          → Expr  Y  ⊢ A
          → Expr  X ++  Y  ⊢ B


module _ (Σ₁ Σ₂ : Vocabulary) where


  private
    module Σ₁ = Vocabulary Σ₁
    open Σ₁ using () renaming
      (Atom to Atom₁;Word to Word₁;Type to Type₁;Judgement to Judgement₁
      ;TypeOf to TypeOf₁;Expr_ to Expr₁_)
    module Σ₂ = Vocabulary Σ₂
    open Σ₂ using () renaming
      (Atom to Atom₂;Word to Word₂;Type to Type₂;Judgement to Judgement₂
      ;TypeOf to TypeOf₂;Expr_ to Expr₂_)

    module Internal-Fᴶ (F : (A : Atom₁) → Type₂) where

      Fᵀ : Type₁ → Type₂
      Fᵀ (Σ₁.el A) = F A
      Fᵀ (A Σ₁.⊸ B) = Fᵀ A Σ₂.⊸ Fᵀ B

      Fᴶ : Judgement₁ → Judgement₂
      Fᴶ (X Σ₁.⊢ A) = map Fᵀ X Σ₂.⊢ Fᵀ A


  record Lexicon : Set where

    field
      F : (A : Atom₁) → Type₂

    open Internal-Fᴶ F public

    field
      G : (x : Word₁) → Expr₂ (∅ Σ₂.⊢ Fᵀ (TypeOf₁ x))

    Fᴱ : ∀ {J} → Expr₁ J → Expr₂ (Fᴶ J)
    Fᴱ  Σ₁.var     = Σ₂.var
    Fᴱ (Σ₁.con x)  = G x
    Fᴱ (Σ₁.abs x)  = Σ₂.abs (Fᴱ x)
    Fᴱ (Σ₁.app {X} {Y} f x)
       = subst (λ X → Expr₂ (X Σ₂.⊢ _))
               (sym (map-++-commute Fᵀ X Y))
               (Σ₂.app (Fᴱ f) (Fᴱ x))


-- -}
-- -}
-- -}
