------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _<_; _≮_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties as NatProps using ()
open import Relation.Binary using (module StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)


module Logic.Classical.Ordered.LambekGrishin.Structure.Complexity {ℓ} (Univ : Set ℓ) where


import Logic.Classical.Ordered.LambekGrishin.Type.Complexity Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ
open StrictTotalOrder NatProps.strictTotalOrder using (irrefl)


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
