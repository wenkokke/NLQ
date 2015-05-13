------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Product                               using (_×_; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Ordered.InSitu.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.InSitu.Type Univ


infix 3 _⊢_


data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement


⊢-injective : ∀ {A B C D} → (A ⊢ B) ≡ (C ⊢ D) → A ≡ C × B ≡ D
⊢-injective refl = refl , refl
