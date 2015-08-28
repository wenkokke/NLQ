--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure/Complexity.agda
--------------------------------------------------------------------------------


open import Data.Nat using (ℕ; suc; _+_)


module Logic.NLCPS.Structure.Complexity {ℓ} (Atom : Set ℓ) where


import Logic.NLCPS.Type.Complexity Atom as T
open import Logic.NLCPS.Structure.Polarised Atom


infix 10 ⌈_⌉ ⌊_⌋

-- Compute the complexity of a type, measured in the number of
-- connectives and atomic formulas in the type.
mutual
  ⌈_⌉ : ∀ {p} → Structure p → ℕ
  ⌈ X ⌉ = suc ⌊ X ⌋

  ⌊_⌋ : ∀ {p} → Structure p → ℕ
  ⌊ · A · ⌋ = T.⌈ A ⌉
  ⌊ ⟨ X ⟩ ⌋ =   ⌈ X ⌉
  ⌊ X ⊗ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⇐ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⇒ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
