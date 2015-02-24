------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

module Logic.Classical.Ordered.LambekGrishin.Structure {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type Univ


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
