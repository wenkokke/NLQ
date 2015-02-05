------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module TypeAndEffect.Type {ℓ} (Univ : Set ℓ) where


infixr 20 ¬_^_ _^_⇒_^_


data Type : Set ℓ where

  el : Univ → Type

  ¬_^_    : Type → Type → Type
  _^_⇒_^_ : Type → Type → Type → Type → Type
