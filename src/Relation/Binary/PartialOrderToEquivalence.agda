------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- A utility module which constructs an equivalence relation from a
-- partial order. This requires some tricks, as the Agda standard
-- library defines orders based on equivalences. Therefore, instead of
-- requiring an instance of the poset class, this module requires an
-- order together with proof of identity and transitivity, and defines
-- an equivalence relation, and a complete instance of the poset class.
------------------------------------------------------------------------


open import Function using (flip)
open import Data.Product using (_×_; _,_; proj₁; proj₂; swap; zip)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary using (Rel; IsPreorder; Preorder; IsPartialOrder; Poset; IsEquivalence)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)


module Relation.Binary.PartialOrderToEquivalence
       {a ℓ} {A : Set a}
       (_≤_ : Rel A ℓ)
       (id : ∀ {x} → x ≤ x)
       (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z) where

-- we can define the equivalence in terms of a product of partial
-- order proofs, which will help with the definition of anti-symmetry.
_≈_ : ∀ x y → Set ℓ
x ≈ y = x ≤ y × y ≤ x

-- we can then easily define an equivalence relation, based on using
-- swap to encode symmetry.
isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl  = id , id
  ; sym   = swap
  ; trans = zip trans (flip trans)
  }

-- and using this equivalence, ≈ easily turns ≤ into a preorder, using
-- the first projection function as reflexivity.
isPreorder : IsPreorder _≈_ _≤_
isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = proj₁
  ; trans         = trans
  }

preorder : Preorder _ _ _
preorder = record { isPreorder = isPreorder }

-- finally, as hinted at above, the pairing function (,) takes the
-- role of the anti-symmetry axiom.
isPartialOrder : IsPartialOrder _≈_ _≤_
isPartialOrder = record
  { isPreorder = isPreorder
  ; antisym    = _,_
  }

poset : Poset _ _ _
poset = record { isPartialOrder = isPartialOrder }
