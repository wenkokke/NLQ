------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Logic.Reification


module Logic.Intuitionistic.Structure.ToAgda
  {ℓ₁ ℓ₂} (Type : Set ℓ₁) (Type→Set : Reify Type (Set ℓ₂)) where


open import Logic.Intuitionistic.Structure Type


⟦_⟧ˢ : List Type → List (Set ℓ₂)
⟦ ∅     ⟧ˢ = ∅
⟦ A , Γ ⟧ˢ = ⟦ A ⟧ᵗ , ⟦ Γ ⟧ˢ
  where
    open Reify Type→Set renaming (⟦_⟧ to ⟦_⟧ᵗ)


instance
  Structure→Set : Reify (List Type) (List (Set ℓ₂))
  Structure→Set = record { ⟦_⟧ = ⟦_⟧ˢ }
