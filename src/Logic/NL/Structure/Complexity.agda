--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure/Complexity.agda
--------------------------------------------------------------------------------


open import Data.Nat using (ℕ; suc; _+_)


module Logic.NL.Structure.Complexity {ℓ} (Atom : Set ℓ) where


import Logic.NL.Type.Complexity Atom as T
open import Logic.NL.Structure.Polarised Atom


infix 10 ⌈_⌉ ⌊_⌋

-- Compute the complexity of a type, measured in the number of
-- connectives and atomic formulas in the type.
mutual
  ⌈_⌉ : ∀ {p} → Structure p → ℕ
  ⌈ A ⌉ = suc ⌊ A ⌋

  ⌊_⌋ : ∀ {p} → Structure p → ℕ
  ⌊ · A · ⌋ = T.⌈ A ⌉
  ⌊ A ⊗ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇐ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇒ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
