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

module Logic.NLP.DispCalc.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NLP.DispCalc.Type Atom


infixr 20 _⇒_
infixl 20 _⇐_
infixr 30 _⊗_
infixr 40 □_ ◇_
infixr 40 ■_ ◆_
infixr 40 ◨_ ⬗_
infixr 40 ◧_ ⬖_


data Structure : Polarity → Set ℓ where
  ·_· : {p  : Polarity} (A  : Type) → Structure p
  _⊗_ : (Γ⁺ : Structure +) (Δ⁺ : Structure +) → Structure +
  _⇒_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure -
  _⇐_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure -

  -- scope islands
  ⟨_⟩ : (Γ⁺ : Structure +) → Structure +

  -- infixation
  □_  : (Γ⁻ : Structure -) → Structure -
  ◇_  : (Γ⁺ : Structure +) → Structure +

  -- extraction
  ■_  : (Γ⁻ : Structure -) → Structure -
  ◆_  : (Γ⁺ : Structure +) → Structure +

  -- quantifier raising
  ◨_  : (Γ⁻ : Structure -) → Structure -
  ⬗_  : (Γ⁺ : Structure +) → Structure +
  ◧_  : (Γ⁻ : Structure -) → Structure -
  ⬖_  : (Γ⁺ : Structure +) → Structure +
  L   : Structure +
  R   : Structure +



-- Symmetries that should hold for these types.
infixl 10 _⋈ˢ

_⋈ˢ : ∀ {p} → Structure p → Structure p
(· A ·) ⋈ˢ = · A ⋈ᵗ ·
(⟨ A ⟩) ⋈ˢ = ⟨ A ⋈ˢ ⟩
(□   A) ⋈ˢ = □ (A ⋈ˢ)
(◇   A) ⋈ˢ = ◇ (A ⋈ˢ)
(■   A) ⋈ˢ = ■ (A ⋈ˢ)
(◆   A) ⋈ˢ = ◆ (A ⋈ˢ)
(◨   A) ⋈ˢ = ◨ (A ⋈ˢ)
(⬗   A) ⋈ˢ = ⬗ (A ⋈ˢ)
(◧   A) ⋈ˢ = ◧ (A ⋈ˢ)
(⬖   A) ⋈ˢ = ⬖ (A ⋈ˢ)
(L    ) ⋈ˢ = R
(R    ) ⋈ˢ = L
(A ⊗ B) ⋈ˢ = (B ⋈ˢ) ⊗ (A ⋈ˢ)
(A ⇒ B) ⋈ˢ = (B ⋈ˢ) ⇐ (A ⋈ˢ)
(B ⇐ A) ⋈ˢ = (A ⋈ˢ) ⇒ (B ⋈ˢ)


⋈ˢ-inv : ∀ {p} (A : Structure p) → (A ⋈ˢ) ⋈ˢ ≡ A
⋈ˢ-inv (· A ·) rewrite ⋈ᵗ-inv A = refl
⋈ˢ-inv (⟨ A ⟩) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (□   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (◇   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (■   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (◆   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (◨   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (⬗   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (◧   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (⬖   A) rewrite ⋈ˢ-inv A = refl
⋈ˢ-inv (L    ) = refl
⋈ˢ-inv (R    ) = refl
⋈ˢ-inv (A ⊗ B) rewrite ⋈ˢ-inv A | ⋈ˢ-inv B = refl
⋈ˢ-inv (A ⇒ B) rewrite ⋈ˢ-inv A | ⋈ˢ-inv B = refl
⋈ˢ-inv (B ⇐ A) rewrite ⋈ˢ-inv A | ⋈ˢ-inv B = refl


-- Contexts.
infixl 10 _[_]
infixl 10 _<_>

data Context (p : Polarity) : (p′ : Polarity) → Set ℓ where
  []   : Context p p
  _<⊗_ : (Γ⁺ : Context p +) (Δ⁺ : Structure +) → Context p +
  _⊗>_ : (Γ⁺ : Structure +) (Δ⁺ : Context p +) → Context p +

_[_] : ∀ {p₁ p₂} (Γ : Context p₁ p₂) (Δ : Structure p₁) → Structure p₂
[]         [ Δ ] = Δ
(Γ′ <⊗ Γ ) [ Δ ] = (Γ′ [ Δ ]) ⊗ Γ
(Γ  ⊗> Γ′) [ Δ ] = Γ ⊗ (Γ′ [ Δ ])

_<_> : ∀ {p₁ p₂ p₃} (X : Context p₁ p₂) (Z : Context p₂ p₃) → Context p₁ p₃
[]       < Z > = Z
(X <⊗ Y) < Z > = X < Z >
(X ⊗> Y) < Z > = Y < Z >
