--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/NLIBC/Structure/Context.agda
--------------------------------------------------------------------------------


open import Level                                 using ()
open import Category.Functor                      using (module RawFunctor; RawFunctor)
open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties.Simple as ℕ       using ()
open import Data.Fin                              using (Fin; suc; zero)
open import Data.Maybe                            using (Maybe; just; nothing)
open import Data.Product                          using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; cong; refl)


module Logic.NLLAM.Structure.Context {ℓ} (Atom : Set ℓ) where


open import Logic.NLLAM.Structure Atom


infixr 5 _∙>_
infixl 5 _<∙_
infixl 6 _[_]

data Context : Set ℓ where
  []    : Context
  _∙>_  : Structure → Context   → Context
  _<∙_  : Context   → Structure → Context

_[_] : Context → Structure → Structure
[]        [ Δ ] = Δ
(Γ ∙> Γ′) [ Δ ] = Γ ∙ (Γ′ [ Δ ])
(Γ <∙ Γ′) [ Δ ] = (Γ [ Δ ]) ∙ Γ′

_<_> : Context → Context → Context
[]       < Δ > = Δ
(q ∙> Γ) < Δ > = q ∙> (Γ < Δ >)
(Γ <∙ q) < Δ > = (Γ < Δ >) <∙ q

<>-def : ∀ Γ Δ p → (Γ [ Δ [ p ] ]) ≡ ((Γ < Δ >) [ p ])
<>-def    []    Δ p = refl
<>-def (_ ∙> Γ) Δ p rewrite <>-def Γ Δ p = refl
<>-def (Γ <∙ _) Δ p rewrite <>-def Γ Δ p = refl


module Membership (_≟-Atom_ : (x y : Atom) → Dec (x ≡ y)) where

  open import Logic.NLLAM.Type Atom as T; open T.DecEq _≟-Atom_

  _∈_ : (p : Type) (Γ : Structure) → Set ℓ
  p ∈ Γ = ∃ (λ (Γ′ : Context) → Γ ≡ (Γ′ [ · p · ]))

  _∈?_ : (p : Type) (Γ : Structure) → Dec (p ∈ Γ)
  p ∈? · q · with q ≟-Type p
  ... | yes p=q rewrite p=q = yes ([] , refl)
  ... | no  p≠q = no (λ { ([] , pr) → p≠q (··-injective pr); (_ ∙> _ , ()); (_ <∙ _ , ())})
  p ∈? (Γ₁ ∙ Γ₂) with p ∈? Γ₁ | p ∈? Γ₂
  ... | yes (Γ′ , pr) | _             = yes (Γ′ <∙ Γ₂ , cong (_∙ Γ₂) pr)
  ... | no        _   | yes (Γ′ , pr) = yes (Γ₁ ∙> Γ′ , cong (Γ₁ ∙_) pr)
  ... | no        pr₁ | no        pr₂ = no λ
    { ([] , ())
    ; (Γ′ <∙ _ , pr) → pr₁ (Γ′ , proj₁ (∙-injective pr))
    ; (_ ∙> Γ′ , pr) → pr₂ (Γ′ , proj₂ (∙-injective pr))
    }
  p ∈? I = no (λ { ([] , ()); (_ ∙> _ , ()); (_ <∙ _ , ())})
  p ∈? B = no (λ { ([] , ()); (_ ∙> _ , ()); (_ <∙ _ , ())})
  p ∈? C = no (λ { ([] , ()); (_ ∙> _ , ()); (_ <∙ _ , ())})
