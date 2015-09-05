------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements the axioms and some derived inference rules.
------------------------------------------------------------------------


open import Data.Product                          using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Logic.NL.PG99.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type         Atom as T
open import Logic.NL.Type.Context Atom as C; open C.Simple using (_[_]; _<_>; <>-assoc; <>-def)


infix 3 _⊢_ ⊢ᴺ_ ⊢ᴾ_

data Sequent : Set ℓ where
  _⊢_ : Type → Type → Sequent
  ⊢ᴺ_ : Context → Sequent
  ⊢ᴾ_ : Context → Sequent
