------------------------------------------------------------------------
-- The Lambek Calculus in Agda
-- This file was automatically generated.
------------------------------------------------------------------------


open import Algebra                                    using (module Monoid)
open import Function                                   using (_∘_)
open import Data.List                                  using (List; _∷_; []; _++_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; subst; subst₂)


module Logic.Intuitionistic.Linear.Lambda.SequentCalculus.Base {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Linear.Lambda.Type      Atom
open import Logic.Intuitionistic.Linear.Lambda.Judgement Atom
open Monoid (Data.List.monoid Type) using (identity; assoc)


infix 1 ILL_

data ILL_ : Judgement → Set ℓ where

  ax   : ∀ {A}
       → ILL A ∷ [] ⊢ A

  cut  : ∀ {Γ Δ A B}
       → ILL     Γ      ⊢ A
       → ILL A ∷      Δ ⊢ B
       → ILL     Γ ++ Δ ⊢ B

  ⇒ᴸ   : ∀ {Γ Δ A B C}
       → ILL         Γ      ⊢ A
       → ILL     B ∷      Δ ⊢ C
       → ILL A ⇒ B ∷ Γ ++ Δ ⊢ C

  ⇒ᴿ   : ∀ {Γ A B}
       → ILL A ∷ Γ ⊢ B
       → ILL     Γ ⊢ A ⇒ B

  ⊗ᴸ   : ∀ {Γ A B C}
       → ILL A ∷ (B ∷ Γ) ⊢ C
       → ILL A ⊗  B ∷ Γ ⊢ C

  ⊗ᴿ   : ∀ {Γ Δ A B}
       → ILL Γ      ⊢ A
       → ILL      Δ ⊢ B
       → ILL Γ ++ Δ ⊢ A ⊗ B

  eᴸ  : ∀ Γ₁ Γ₂ Γ₃ Γ₄ {A}
      → ILL (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A
      → ILL (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A


-- Lemma: weaker versions of eᴸ which only swap the first two
-- (or three) elements are often useful.
eᴸ₁  : ∀ {Γ A B C}
     → ILL B ∷ (A ∷ Γ) ⊢ C
     → ILL A ∷ (B ∷ Γ) ⊢ C
eᴸ₁  = eᴸ [] (_ ∷ []) (_ ∷ []) _


-- Lemma: weaker version of eᴸ and eᴿ which only swap two contexts,
-- without allowing them to be embedded in further contexts are often
-- useful as well.
sᴸ  : ∀ (Γ : List Type) {Δ : List Type} {A} → ILL Δ ++ Γ ⊢ A → ILL Γ ++ Δ ⊢ A
sᴸ  Γ {[]} = subst  (λ Γ → ILL Γ ⊢ _) (sym (proj₂ identity Γ))
sᴸ  [] {Δ} = subst  (λ Γ → ILL Γ ⊢ _)      (proj₂ identity Δ)
sᴸ  Γ {Δ} = subst₂ (λ Γ′ Δ′ → ILL Δ ++ Γ′ ⊢ _ → ILL Γ ++ Δ′ ⊢ _) (proj₂ identity Γ) (proj₂ identity Δ) (eᴸ [] Γ Δ [])


-- Lemma: introduction and elimination of right-handed empty context.
[]ᵢ : ∀ {Γ A} → ILL Γ      ⊢ A → ILL Γ ++ [] ⊢ A
[]ᵢ {Γ} f rewrite proj₂ identity Γ = f
[]ₑ : ∀ {Γ A} → ILL Γ ++ [] ⊢ A → ILL Γ      ⊢ A
[]ₑ {Γ} f rewrite proj₂ identity Γ = f
