------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import Logic.Reification


module Logic.Intuitionistic.Judgement.ToAgda
  {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (Univ→Set : Reify Univ (Set ℓ₂)) where


open import Logic.Intuitionistic.Type             Univ
open import Logic.Intuitionistic.Type.ToAgda      Univ Univ→Set
open import Logic.Intuitionistic.Structure        Univ
open import Logic.Intuitionistic.Structure.ToAgda Univ Univ→Set
open import Logic.Intuitionistic.Judgement        Univ
open import Logic.Intuitionistic.Agda.Environment Univ Univ→Set


instance
  Judgement→Set : Reify Judgement (Set ℓ₂)
  Judgement→Set = record { ⟦_⟧ = ⟦_⟧′ }
    where
      open Reify Type→Set renaming (⟦_⟧ to ⟦_⟧ᵗ)
      open Reify Structure→Set renaming (⟦_⟧ to ⟦_⟧ˢ)
      ⟦_⟧′ : Judgement → Set ℓ₂
      ⟦ Γ ⊢ A ⟧′ = Env ((¬ ⟦ A ⟧ᵗ) ∷ ⟦ Γ ⟧ˢ) → ⊥
