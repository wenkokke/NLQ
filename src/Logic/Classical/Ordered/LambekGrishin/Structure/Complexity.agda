------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Nat using (ℕ; suc; _+_)


module Logic.Classical.Ordered.LambekGrishin.Structure.Complexity {ℓ} (Univ : Set ℓ) where


import Logic.Classical.Ordered.LambekGrishin.Type.Complexity Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ


infix 10 ⌈_⌉ ⌊_⌋

-- Compute the complexity of a type, measured in the number of
-- connectives and atomic formulas in the type.
mutual
  ⌈_⌉ : ∀ {p} → Structure p → ℕ
  ⌈ A ⌉ = suc ⌊ A ⌋

  ⌊_⌋ : ∀ {p} → Structure p → ℕ
  ⌊ · A · ⌋ = T.⌈ A ⌉
  ⌊ [ A ] ⌋ =   ⌈ A ⌉
  ⌊ ⟨ A ⟩ ⌋ =   ⌈ A ⌉
  ⌊ ₀   A ⌋ =   ⌈ A ⌉
  ⌊ A   ⁰ ⌋ =   ⌈ A ⌉
  ⌊ ₁   A ⌋ =   ⌈ A ⌉
  ⌊ A   ¹ ⌋ =   ⌈ A ⌉
  ⌊ A ⊗ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇚ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇛ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⊕ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇐ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇒ B ⌋ =   ⌈ A ⌉ + ⌈ B ⌉
