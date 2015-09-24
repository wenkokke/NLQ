------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.LG.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type Atom


infix  10 ·_·
infix  15 [_]
infix  15 ⟨_⟩
infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇚_
infixr 25 _⇛_
infixr 30 _⊗_
infixr 30 _⊕_


data Structure : Set ℓ where
  ·_· : Type      → Structure
  [_] : Structure → Structure
  ⟨_⟩ : Structure → Structure
  ₀_  : Structure → Structure
  _⁰  : Structure → Structure
  ₁_  : Structure → Structure
  _¹  : Structure → Structure
  _⇒_ : Structure → Structure → Structure
  _⇐_ : Structure → Structure → Structure
  _⇚_ : Structure → Structure → Structure
  _⇛_ : Structure → Structure → Structure
  _⊗_ : Structure → Structure → Structure
  _⊕_ : Structure → Structure → Structure


open import Algebra.FunctionProperties {A = Structure} _≡_


_⋈ˢ : Structure → Structure
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


_∞ˢ : Structure → Structure
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


⋈ˢ-inv : Involutive _⋈ˢ
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


∞ˢ-inv : Involutive _∞ˢ
∞ˢ-inv ·  A  · rewrite ∞-inv A = refl
∞ˢ-inv [  X  ] rewrite ∞ˢ-inv X = refl
∞ˢ-inv ⟨  X  ⟩ rewrite ∞ˢ-inv X = refl
∞ˢ-inv (₀   X) rewrite ∞ˢ-inv X = refl
∞ˢ-inv (X   ⁰) rewrite ∞ˢ-inv X = refl
∞ˢ-inv (₁   X) rewrite ∞ˢ-inv X = refl
∞ˢ-inv (X   ¹) rewrite ∞ˢ-inv X = refl
∞ˢ-inv (X ⇒ Y) rewrite ∞ˢ-inv X | ∞ˢ-inv Y = refl
∞ˢ-inv (X ⇐ Y) rewrite ∞ˢ-inv X | ∞ˢ-inv Y = refl
∞ˢ-inv (X ⇚ Y) rewrite ∞ˢ-inv X | ∞ˢ-inv Y = refl
∞ˢ-inv (X ⇛ Y) rewrite ∞ˢ-inv X | ∞ˢ-inv Y = refl
∞ˢ-inv (X ⊗ Y) rewrite ∞ˢ-inv X | ∞ˢ-inv Y = refl
∞ˢ-inv (X ⊕ Y) rewrite ∞ˢ-inv X | ∞ˢ-inv Y = refl
