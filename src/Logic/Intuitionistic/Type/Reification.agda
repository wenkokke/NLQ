------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Logic.Reification


module Logic.Intuitionistic.Type.ToAgda
    {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (Univ→Set : Reify Univ (Set ℓ₂)) where


open import Logic.Intuitionistic.Type Univ


Type→Set : Reify Type (Set ℓ₂)
Type→Set = record { ⟦_⟧ = _* }
  where
    infix 5 _*

    _* : Type → Set ℓ₂
    el A  * = ⟦ A ⟧
    A ⇒ B * = ¬  B * → ¬ A *
    A ⇛ B * = ¬  B * ×   A *
    A ⊗ B * = ¬ (B * ×   A *)
