------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function
open import Data.Bool                             using (Bool; true; false; _∧_)
open import Data.Fin                              using (Fin; suc; zero; #_; toℕ)
open import Data.List                             using (List; map; all; any; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Nat                              using (ℕ; suc; zero)
open import Data.Product                          using (_,_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.Lexicon where

Entity = Fin 3

open import Example.Base Entity public

abstract
  domainₑ : List Entity
  domainₑ = go
    where
      go : ∀ {n} → List (Fin n)
      go {zero } = ∅
      go {suc n} = zero , map suc go

  forallₑ : (Entity → Bool) → Bool
  forallₑ p = all p domainₑ

  existsₑ : (Entity → Bool) → Bool
  existsₑ p = any p domainₑ

  john mary bill : Entity
  john = # 0
  bill = # 1
  mary = # 2

  _loves_ : Entity → Entity → Bool
  zero     loves suc zero       = true
  suc zero loves zero           = true
  suc zero loves suc zero       = true
  suc zero loves suc (suc zero) = true
  _        loves _              = false

  _left : Entity → Bool
  zero  left = true
  suc _ left = false

  person : Entity → Bool
  person _ = true

  postulate
    _thinks_ : Entity → Bool → Bool



-- specific to lambek-grishin

JOHN BILL MARY LOVES THINKS LEFT PERSON : Type
JOHN   = np
BILL   = np
MARY   = np
LOVES  = (np ⇒ s⁻) ⇐ np
THINKS = (np ⇒ s⁻) ⇐ s⁻
LEFT   = np ⇒ s⁻
PERSON = n

loves′  : ⟦ LOVES ⟧ᵀ
loves′  ((x , k) , y) = k (x loves y)
left′   : ⟦ LEFT ⟧ᵀ
left′    (x , k)      = k (x left)
thinks′ : ⟦ THINKS ⟧ᵀ
thinks′ ((x , k) , y) = k (x thinks (y id))
