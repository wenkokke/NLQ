------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Nat using (ℕ; suc; _+_)


module Logic.LG.Structure.Complexity {ℓ} (Atom : Set ℓ) where


import Logic.LG.Type.Complexity Atom as T
open import Logic.LG.Structure.Polarised Atom


infix 10 ⌈_⌉ ⌊_⌋

-- Compute the complexity of a type, measured in the number of
-- connectives and atomic formulas in the type.
mutual
  ⌈_⌉ : ∀ {p} → Structure p → ℕ
  ⌈ X ⌉ = suc ⌊ X ⌋

  ⌊_⌋ : ∀ {p} → Structure p → ℕ
  ⌊ · A · ⌋ = T.⌈ A ⌉
  ⌊ [ X ] ⌋ =   ⌈ X ⌉
  ⌊ ⟨ X ⟩ ⌋ =   ⌈ X ⌉
  ⌊ ₀   X ⌋ =   ⌈ X ⌉
  ⌊ X   ⁰ ⌋ =   ⌈ X ⌉
  ⌊ ₁   X ⌋ =   ⌈ X ⌉
  ⌊ X   ¹ ⌋ =   ⌈ X ⌉
  ⌊ X ⊗ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⇚ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⇛ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⊕ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⇐ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
  ⌊ X ⇒ Y ⌋ =   ⌈ X ⌉ + ⌈ Y ⌉
