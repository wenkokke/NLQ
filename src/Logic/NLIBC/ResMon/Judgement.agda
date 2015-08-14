------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product                               using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.NLIBC.ResMon.Judgement {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type Atom


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement


⊢-injective : ∀ {x y z w} → (x ⊢ y) ≡ (z ⊢ w) → x ≡ z × y ≡ w
⊢-injective refl = refl , refl
