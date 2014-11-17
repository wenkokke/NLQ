------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Logic.Reification


module Logic.Intuitionistic.Structure.ToAgda
  {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (Univ→Set : Reify Univ (Set ℓ₂)) where


open import Logic.Intuitionistic.Type        Univ
open import Logic.Intuitionistic.Type.ToAgda Univ Univ→Set
open import Logic.Intuitionistic.Structure   Univ using (List; ∅; _,_)


instance
  Structure→Set : Reify (List Type) (List (Set ℓ₂))
  Structure→Set = record { ⟦_⟧ = ⟦_⟧′ }
    where
      ⟦_⟧′ : List Type → List (Set ℓ₂)
      ⟦ ∅     ⟧′ = ∅
      ⟦ A , Γ ⟧′ = ⟦ A ⟧ , ⟦ Γ ⟧′
