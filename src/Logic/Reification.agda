------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Data.List as List using (List)
open import Data.Vec as Vec using (Vec)

module Logic.Reification where


record Reify {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    ⟦_⟧ : A → B


open Reify {{...}} public


instance
  ReifyList : ∀ {a b A B} {{dict : Reify {a} {b} A B}} → Reify (List A) (List B)
  ReifyList {{dict}} = record { ⟦_⟧ = List.map ⟦_⟧ }


instance
  ReifyVec : ∀ {a b A B} {{dict : Reify {a} {b} A B}} {k} → Reify (Vec A k) (Vec B k)
  ReifyVec {{dict}} = record { ⟦_⟧ = Vec.map ⟦_⟧ }
