------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Ordered.InSitu.Type {ℓ} (Univ : Set ℓ) where


infixr 20 _⊗_ _∘_
infixr 30 _⇒_ _⇨_
infixl 30 _⇐_ _⇦_
infix  40 □_ ◇_


data Type : Set ℓ where

  el  : Univ → Type

  ◇_  : Type → Type
  □_  : Type → Type

  _⊗_ : Type → Type → Type
  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type

  _∘_ : Type → Type → Type
  _⇨_ : Type → Type → Type
  _⇦_ : Type → Type → Type

  I   : Type
  L   : Type
  R   : Type
