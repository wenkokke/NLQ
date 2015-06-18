------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra      using (module Monoid)
open import Data.Fin     using (Fin; suc; zero; #_)
open import Data.List    using (List; _∷_; []; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)


module Logic.Intuitionistic.Unrestricted.Lambda.Indexed.Base {ℓ} (Atom : Set ℓ) where


open import Logic.Index
open import Logic.Intuitionistic.Unrestricted.Lambda.Type      Atom
open import Logic.Intuitionistic.Unrestricted.Lambda.Judgement Atom
open Monoid (Data.List.monoid Type) using (identity; assoc)


infix 1 Λ_

data Λ_ : Judgement → Set ℓ where

  ax : ∀ {Γ} (x : Fin _)
     → Λ Γ ⊢ Γ ‼ x

  ⇒ᵢ : ∀ {Γ A B}
     → Λ A ∷ Γ ⊢ B
     → Λ     Γ ⊢ A ⇒ B

  ⇒ₑ : ∀ {Γ A B}
     → Λ Γ ⊢ A ⇒ B
     → Λ Γ ⊢ A
     → Λ Γ ⊢ B

  ⊗ᵢ : ∀ {Γ A B}
     → Λ Γ ⊢ A
     → Λ Γ ⊢ B
     → Λ Γ ⊢ A ⊗ B

  ⊗ₑ : ∀ {Γ A B C}
     → Λ          Γ  ⊢ A ⊗ B
     → Λ A ∷ (B ∷ Γ) ⊢ C
     → Λ          Γ  ⊢ C


-- Theorem:
--   eᴸ shows that the structural rule of exchange is implicit in the
--   axiomatisation that we've chosen.
eᴸ′ : ∀ Γ₁ Γ₂ Γ₃ Γ₄ {A}
    → Λ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A
    → Λ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A
eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (ax x)   with (exchange Γ₁ Γ₂ Γ₃ Γ₄ x)
eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (ax x)   | y , p rewrite p = ax y
eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (⇒ᵢ f)   = ⇒ᵢ (eᴸ′ (_ ∷ Γ₁) Γ₂ Γ₃ Γ₄ f)
eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (⇒ₑ f g) = ⇒ₑ (eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ′           Γ₁   Γ₂ Γ₃ Γ₄ g)
eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (⊗ᵢ f g) = ⊗ᵢ (eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ′           Γ₁   Γ₂ Γ₃ Γ₄ g)
eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ (⊗ₑ f g) = ⊗ₑ (eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ′ (_ ∷ (_ ∷ Γ₁)) Γ₂ Γ₃ Γ₄ g)


-- Lemma:
--   weaker versions of eᴸ which only swap the first two (or three)
--   elements are often useful.
eᴸ₁′ : ∀ {Γ A B C}
     → Λ B ∷ (A ∷ Γ) ⊢ C
     → Λ A ∷ (B ∷ Γ) ⊢ C
eᴸ₁′ = eᴸ′ [] (_ ∷ []) (_ ∷ []) _

eᴸ₂′ : ∀ {Γ A B C D}
     → Λ C ∷ (A ∷ (B ∷ Γ)) ⊢ D
     → Λ A ∷ (B ∷ (C ∷ Γ)) ⊢ D
eᴸ₂′ = eᴸ′ [] (_ ∷ (_ ∷ [])) (_ ∷ []) _


-- Lemma:
--   weaker version of eᴸ and eᴿ which only swap two contexts∷ without
--   allowing them to be embedded in further contexts are often useful
--   as well.
sᴸ′ : ∀ (Γ₁ : List Type) {Γ₂ : List Type} {A}
    → Λ Γ₂ ++ Γ₁ ⊢ A
    → Λ Γ₁ ++ Γ₂ ⊢ A
sᴸ′ Γ₁ {[] } = subst  (λ Γ → Λ Γ   ⊢ _) (sym (proj₂ identity Γ₁))
sᴸ′ []  {Γ₂} = subst  (λ Γ   → Λ Γ ⊢ _) (proj₂ identity Γ₂)
sᴸ′ Γ₁ {Γ₂} = subst₂ (λ Γ₁′ Γ₂′ → Λ Γ₂ ++ Γ₁′ ⊢ _ → Λ Γ₁ ++ Γ₂′ ⊢ _) (proj₂ identity Γ₁ ) (proj₂ identity Γ₂) (eᴸ′  [] Γ₁ Γ₂ [])



-- Lemma:
--   weaker version of weakning for which simply allows for the
--   addition of one unused premise can easily be induced from the
--   axioms.
wᴸ₁′  : ∀ {Γ A B}
     → Λ     Γ ⊢ B
     → Λ A ∷ Γ ⊢ B
wᴸ₁′ (ax  x)   = ax (suc x)
wᴸ₁′ (⇒ᵢ  f)   = ⇒ᵢ (eᴸ₁′ (wᴸ₁′ f))
wᴸ₁′ (⇒ₑ  f g) = ⇒ₑ (wᴸ₁′  f) (wᴸ₁′ g)
wᴸ₁′ (⊗ᵢ  f g) = ⊗ᵢ (wᴸ₁′  f) (wᴸ₁′ g)
wᴸ₁′ (⊗ₑ  f g) = ⊗ₑ (wᴸ₁′  f) (eᴸ₂′ (wᴸ₁′ g))


-- Theorem:
--   full weakening follows easily by induction from the simplified
--   version of weakening proved above.
wᴸ′ : ∀ Γ₁ {Γ₂ A}
    → Λ       Γ₂ ⊢ A
    → Λ Γ₁ ++ Γ₂ ⊢ A
wᴸ′      []   f = f
wᴸ′ (A ∷ Γ₁) f = wᴸ₁′ (wᴸ′  Γ₁ f)


-- Lemma:
--   weaker version of contraction∷ which contract two values of the
--   same type, can easily be derived from the axioms.
cᴸ₁′ : ∀ {Γ A B}
     → Λ A ∷ (A ∷ Γ) ⊢ B
     → Λ      A ∷ Γ  ⊢ B
cᴸ₁′ f = ⇒ₑ (⇒ᵢ f) (ax (# 0))


-- Theorem:
--   contraction of identical contexts follows easily by induction
--   from the derived rules for contaction above.
cᴸ′ : ∀ (Γ₁ Γ₂ : List Type) {A}
    → Λ Γ₁ ++ Γ₁ ++ Γ₂ ⊢ A
    → Λ Γ₁       ++ Γ₂ ⊢ A
cᴸ′      []   Γ₂ f = f
cᴸ′ (A ∷ Γ₁) Γ₂ f = eᴸ′ [] (A ∷ []) Γ₁ Γ₂ (cᴸ′ Γ₁ (A ∷ Γ₂) lem₁)
  where
    lem₀ : Λ A ∷ (Γ₁ ++ Γ₁) ++ Γ₂ ⊢ _
    lem₀ rewrite      assoc Γ₁ Γ₁      Γ₂   = cᴸ₁′ (eᴸ′ [] (A ∷ []) (A ∷ Γ₁) (Γ₁ ++ Γ₂) f)
    lem₁ : Λ Γ₁ ++ (Γ₁ ++ A ∷ Γ₂) ⊢ _
    lem₁ rewrite sym (assoc Γ₁ Γ₁ (A ∷ Γ₂)) = eᴸ′ [] (Γ₁ ++ Γ₁) (A ∷ []) Γ₂ lem₀
