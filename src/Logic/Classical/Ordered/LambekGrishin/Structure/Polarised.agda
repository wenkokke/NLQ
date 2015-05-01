------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Structure.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type      Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure Univ
            as Unpolarised hiding (module Structure; Structure)


infix  10 ·_·
infix  15 [_] ⟨_⟩
infixr 20 _⇒_ _⇐_
infixl 25 _⇚_ _⇛_
infixr 30 _⊗_ _⊕_


data Structure : Polarity → Set ℓ where
  ·_· : {p  : Polarity}    (A  : Type)        → Structure p
  [_] : (Γ⁻ : Structure -)                    → Structure -
  ⟨_⟩ : (Γ⁺ : Structure +)                    → Structure +
  ₀_  : (Γ⁻ : Structure +)                    → Structure -
  _⁰  : (Γ⁻ : Structure +)                    → Structure -
  ₁_  : (Γ⁺ : Structure -)                    → Structure +
  _¹  : (Γ⁺ : Structure -)                    → Structure +
  _⊗_ : (Γ⁺ : Structure +) (Δ⁺ : Structure +) → Structure +
  _⇚_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure +
  _⇛_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure +
  _⊕_ : (Γ⁻ : Structure -) (Δ⁻ : Structure -) → Structure -
  _⇒_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure -
  _⇐_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure -


data Polarised : Polarity → Unpolarised.Structure → Set ℓ where
  ·_· : ∀ {p}   (A  : Type)                               → Polarised p (· A ·)
  [_] : ∀ {Γ}   (Γ⁻ : Polarised - Γ)                      → Polarised - ([ Γ ])
  ⟨_⟩ : ∀ {Γ}   (Γ⁺ : Polarised + Γ)                      → Polarised + (⟨ Γ ⟩)
  ₀_  : ∀ {Γ}   (Γ⁻ : Polarised + Γ)                      → Polarised - (₀   Γ)
  _⁰  : ∀ {Γ}   (Γ⁻ : Polarised + Γ)                      → Polarised - (Γ   ⁰)
  ₁_  : ∀ {Γ}   (Γ⁺ : Polarised - Γ)                      → Polarised + (₁   Γ)
  _¹  : ∀ {Γ}   (Γ⁺ : Polarised - Γ)                      → Polarised + (Γ   ¹)
  _⊗_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⊗ Δ)
  _⇚_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised + (Γ ⇚ Δ)
  _⇛_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⇛ Δ)
  _⊕_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⊕ Δ)
  _⇒_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⇒ Δ)
  _⇐_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised - (Γ ⇐ Δ)


module Correct where

  forget : ∀ {p} (Γᴾ : Structure p) → Unpolarised.Structure
  forget (· A ·) = · A ·
  forget ([ Γ ]) = [ forget Γ ]
  forget (⟨ Γ ⟩) = ⟨ forget Γ ⟩
  forget (₀   Γ) = ₀ forget Γ
  forget (Γ   ⁰) = forget Γ ⁰
  forget (₁   Γ) = ₁ forget Γ
  forget (Γ   ¹) = forget Γ ¹
  forget (Γ ⊗ Δ) = forget Γ ⊗ forget Δ
  forget (Γ ⇚ Δ) = forget Γ ⇚ forget Δ
  forget (Γ ⇛ Δ) = forget Γ ⇛ forget Δ
  forget (Γ ⊕ Δ) = forget Γ ⊕ forget Δ
  forget (Γ ⇒ Δ) = forget Γ ⇒ forget Δ
  forget (Γ ⇐ Δ) = forget Γ ⇐ forget Δ

  forget-correct : ∀ {p} (Γᴾ : Structure p) → Polarised p (forget Γᴾ)
  forget-correct ·  A  · = · A ·
  forget-correct [  Γ  ] = [ forget-correct Γ ]
  forget-correct ⟨  Γ  ⟩ = ⟨ forget-correct Γ ⟩
  forget-correct (₀   Γ) = ₀ forget-correct Γ
  forget-correct (Γ   ⁰) = forget-correct Γ ⁰
  forget-correct (₁   Γ) = ₁ forget-correct Γ
  forget-correct (Γ   ¹) = forget-correct Γ ¹
  forget-correct (Γ ⊗ Δ) = forget-correct Γ ⊗ forget-correct Δ
  forget-correct (Γ ⇚ Δ) = forget-correct Γ ⇚ forget-correct Δ
  forget-correct (Γ ⇛ Δ) = forget-correct Γ ⇛ forget-correct Δ
  forget-correct (Γ ⊕ Δ) = forget-correct Γ ⊕ forget-correct Δ
  forget-correct (Γ ⇒ Δ) = forget-correct Γ ⇒ forget-correct Δ
  forget-correct (Γ ⇐ Δ) = forget-correct Γ ⇐ forget-correct Δ
