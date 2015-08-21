------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements the axioms and some derived inference rules.
------------------------------------------------------------------------


open import Data.Product                          using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Logic.NL.PG99.Judgement {ℓ} (Atom : Set ℓ) where


open import Logic.NL.Type         Atom as T
open import Logic.NL.Type.Context Atom as C; open C.Simple using (_[_]; _<_>; <>-assoc; <>-def)


infix 3 _⊢_ ⊢ᴺ_ ⊢ᴾ_

data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement
  ⊢ᴺ_ : Context → Judgement
  ⊢ᴾ_ : Context → Judgement
