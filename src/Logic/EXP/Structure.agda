--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure.agda
--------------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.EXP.Structure {ℓ} (Atom : Set ℓ) where


open import Logic.EXP.Type Atom


infix  10 ·_·
infix  15 ⟨_⟩
infixr 20 _⇒_
infixl 20 _⇐_
infixr 30 _⊗_
data Structure : Set ℓ where

  ·_· : Type      → Structure
  ⟨_⟩ : Structure → Structure
  _⇒_ : Structure → Structure → Structure
  _⇐_ : Structure → Structure → Structure
  _⊗_ : Structure → Structure → Structure
open import Algebra.FunctionProperties {A = Structure} _≡_


_⋈ˢ : Structure → Structure
(· A ·) ⋈ˢ = · A ⋈ ·
(⟨ X ⟩) ⋈ˢ = ⟨ X ⋈ˢ ⟩
(X ⊗ Y) ⋈ˢ = (Y ⋈ˢ) ⊗ (X ⋈ˢ)
(X ⇒ Y) ⋈ˢ = (Y ⋈ˢ) ⇐ (X ⋈ˢ)
(Y ⇐ X) ⋈ˢ = (X ⋈ˢ) ⇒ (Y ⋈ˢ)
⋈ˢ-inv : Involutive _⋈ˢ
⋈ˢ-inv ·  A  · rewrite ⋈-inv A = refl
⋈ˢ-inv ⟨  X  ⟩ rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X ⇒ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇐ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⊗ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
