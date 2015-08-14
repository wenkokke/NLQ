--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Type/Complexity.agda
--------------------------------------------------------------------------------


open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _<_; _≮_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties as NatProps using ()
open import Relation.Binary using (module StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open StrictTotalOrder NatProps.strictTotalOrder using (irrefl)


module Logic.MM96.Type.Complexity {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type Atom


infix 10 ⌈_⌉ ⌊_⌋

-- Compute the complexity of a type, measured in the number of
-- connectives and atomic formulas in the type.
mutual
  ⌈_⌉ : Type → ℕ
  ⌈ A ⌉ = suc ⌊ A ⌋

  ⌊_⌋ : Type → ℕ
  ⌊ el  A ⌋ = zero
  ⌊ ⟨t⟩   ⌋ = zero
  ⌊ ⟨l⟩ A ⌋ = ⌈ A ⌉
  ⌊ ⟨r⟩ A ⌋ = ⌈ A ⌉
  ⌊ ◇   A ⌋ = ⌈ A ⌉
  ⌊ □   A ⌋ = ⌈ A ⌉
  ⌊ A ⊗ B ⌋ = ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇦ B ⌋ = ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇨ B ⌋ = ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⊙ B ⌋ = ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇐ B ⌋ = ⌈ A ⌉ + ⌈ B ⌉
  ⌊ A ⇒ B ⌋ = ⌈ A ⌉ + ⌈ B ⌉


-- Lemma which shows that if types are not of the same complexity,
-- then they cannot be equal.
⌈A⌉<⌈B⌉→A≠B : ∀ A B → ⌈ A ⌉ < ⌈ B ⌉ → A ≢ B
⌈A⌉<⌈B⌉→A≠B A B ⌈A⌉<⌈B⌉ A=B = irrefl (cong ⌈_⌉ A=B) ⌈A⌉<⌈B⌉
