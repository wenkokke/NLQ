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


--------------------------------------------------------------------------------
-- TODO: Triggers an Agda bug in Substitute.hs
--------------------------------------------------------------------------------
{-
record ACG {τ₁ ℓ₁ τ₂ ℓ₂ : Level}
           {T₁ : Set τ₁} (L₁ : T₁ → Set ℓ₁)
           {T₂ : Set τ₂} (L₂ : T₂ → Set ℓ₂) : Set (τ₁ ⊔ ℓ₁ ⊔ τ₂ ⊔ ℓ₂ ) where

  field
    T₁→T₂ : Reify T₁ T₂
    L₁→L₂ : {A : T₁} → Reify (L₁ A) (L₂ (⟦ A ⟧))

  [_] : ∀ {A} → L₁ A → L₂ (Reify.⟦ T₁→T₂ ⟧ A)
  [_] = Reify.⟦ L₁→L₂ ⟧


open ACG {{...}} public using (T₁→T₂; [_])
-}
--------------------------------------------------------------------------------
