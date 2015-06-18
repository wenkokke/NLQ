------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; cong; cong₂)


module Logic.Classical.Ordered.LambekGrishin.Structure.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type      Atom
open import Logic.Classical.Ordered.LambekGrishin.Structure Atom
     as Unpolarised hiding (module Structure; Structure; _⋈ˢ; _∞ˢ; ⋈ˢ-inv; ∞ˢ-inv)


infix  10 ·_·
infix  15 [_] ⟨_⟩
infixr 20 _⇒_ _⇐_
infixl 25 _⇚_ _⇛_
infixr 30 _⊗_ _⊕_
infixl 50 _⋈ˢ _∞ˢ


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


_⋈ˢ : ∀ {p} → Structure p → Structure p
(· A ·) ⋈ˢ = · A ⋈ ·
([ X ]) ⋈ˢ = [ X ⋈ˢ ]
(⟨ X ⟩) ⋈ˢ = ⟨ X ⋈ˢ ⟩
(₀   X) ⋈ˢ = (X ⋈ˢ)   ⁰
(X   ⁰) ⋈ˢ = ₀       (X ⋈ˢ)
(₁   X) ⋈ˢ = (X ⋈ˢ)   ¹
(X   ¹) ⋈ˢ = ₁       (X ⋈ˢ)
(X ⊗ Y) ⋈ˢ = (Y ⋈ˢ) ⊗ (X ⋈ˢ)
(X ⇒ Y) ⋈ˢ = (Y ⋈ˢ) ⇐ (X ⋈ˢ)
(Y ⇐ X) ⋈ˢ = (X ⋈ˢ) ⇒ (Y ⋈ˢ)
(Y ⊕ X) ⋈ˢ = (X ⋈ˢ) ⊕ (Y ⋈ˢ)
(Y ⇚ X) ⋈ˢ = (X ⋈ˢ) ⇛ (Y ⋈ˢ)
(X ⇛ Y) ⋈ˢ = (Y ⋈ˢ) ⇚ (X ⋈ˢ)


_∞ˢ : ∀ {p} → Structure p → Structure (~ p)
(· A ·) ∞ˢ = · A ∞ ·
([ X ]) ∞ˢ = ⟨ X ∞ˢ ⟩
(⟨ X ⟩) ∞ˢ = [ X ∞ˢ ]
(₀   X) ∞ˢ = (X ∞ˢ)   ¹
(X   ⁰) ∞ˢ = ₁       (X ∞ˢ)
(₁   X) ∞ˢ = (X ∞ˢ)   ⁰
(X   ¹) ∞ˢ = ₀       (X ∞ˢ)
(X ⊗ Y) ∞ˢ = (Y ∞ˢ) ⊕ (X ∞ˢ)
(X ⇒ Y) ∞ˢ = (Y ∞ˢ) ⇚ (X ∞ˢ)
(Y ⇐ X) ∞ˢ = (X ∞ˢ) ⇛ (Y ∞ˢ)
(Y ⊕ X) ∞ˢ = (X ∞ˢ) ⊗ (Y ∞ˢ)
(Y ⇚ X) ∞ˢ = (X ∞ˢ) ⇒ (Y ∞ˢ)
(X ⇛ Y) ∞ˢ = (Y ∞ˢ) ⇐ (X ∞ˢ)


⋈ˢ-inv : ∀ {p} (X : Structure p) → (X ⋈ˢ) ⋈ˢ ≡ X
⋈ˢ-inv ·  A  · rewrite ⋈-inv A = refl
⋈ˢ-inv [  X  ] rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv ⟨  X  ⟩ rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (₀   X) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X   ⁰) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (₁   X) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X   ¹) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X ⇒ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇐ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇚ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇛ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⊗ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⊕ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl


∞ˢ-inv : ∀ {p} (X : Structure p) → (X ∞ˢ) ∞ˢ ≅ X
∞ˢ-inv { p } ·  A  · rewrite ~-inv p | ∞-inv A = refl
∞ˢ-inv { - } [  X  ] = cong  [_] (∞ˢ-inv X)
∞ˢ-inv { + } ⟨  X  ⟩ = cong  ⟨_⟩ (∞ˢ-inv X)
∞ˢ-inv { - } (₀   X) = cong   ₀_ (∞ˢ-inv X)
∞ˢ-inv { - } (X   ⁰) = cong  _⁰  (∞ˢ-inv X)
∞ˢ-inv { + } (₁   X) = cong   ₁_ (∞ˢ-inv X)
∞ˢ-inv { + } (X   ¹) = cong  _¹  (∞ˢ-inv X)
∞ˢ-inv { + } (X ⊗ Y) = cong₂ _⊗_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { - } (X ⇒ Y) = cong₂ _⇒_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { - } (X ⇐ Y) = cong₂ _⇐_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { - } (X ⊕ Y) = cong₂ _⊕_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { + } (X ⇚ Y) = cong₂ _⇚_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { + } (X ⇛ Y) = cong₂ _⇛_ (∞ˢ-inv X) (∞ˢ-inv Y)


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
