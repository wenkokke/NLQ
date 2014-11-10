------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Nat as Nat using (ℕ; suc; zero; _+_; _<_; _≮_; _≥_; s≤s; z≤n)
open import Data.Nat.Properties as NatProps using ()
open import Relation.Binary using (module StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)


module Logic.Lambek.Type.Complexity {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type Univ
open StrictTotalOrder NatProps.strictTotalOrder using (irrefl)


infix 10 ∣_∣

-- Compute the complexity of a type, measured in the number of
-- connectives and atomic formulas in the type.
∣_∣ : Type → ℕ
∣ el A ∣  = suc zero
∣ A ⊗ B ∣ = suc (∣ A ∣ + ∣ B ∣)
∣ A ⇐ B ∣ = suc (∣ A ∣ + ∣ B ∣)
∣ A ⇒ B ∣ = suc (∣ A ∣ + ∣ B ∣)


-- Lemma which shows that any type has a complexity of at least one.
∣A∣≥1 : ∀ A → ∣ A ∣ ≥ 1
∣A∣≥1 (el _)  = s≤s z≤n
∣A∣≥1 (_ ⊗ _) = s≤s z≤n
∣A∣≥1 (_ ⇐ _) = s≤s z≤n
∣A∣≥1 (_ ⇒ _) = s≤s z≤n


-- Lemma which shows that no type has strictly lower complexity than
-- elementary types.
∣A∣≮∣elB∣ : ∀ A B → ∣ A ∣ ≮ ∣ el B ∣
∣A∣≮∣elB∣ (el A)    B (s≤s ())
∣A∣≮∣elB∣ (A₁ ⊗ A₂) B (s≤s ())
∣A∣≮∣elB∣ (A₁ ⇒ A₂) B (s≤s ())
∣A∣≮∣elB∣ (A₁ ⇐ A₂) B (s≤s ())


-- Lemma which shows that if types are not of the same complexity,
-- then they cannot be equal.
∣A∣<∣B∣→A≠B : ∀ A B → ∣ A ∣ < ∣ B ∣ → A ≢ B
∣A∣<∣B∣→A≠B A B ∣A∣<∣B∣ A=B = irrefl (cong ∣_∣ A=B) ∣A∣<∣B∣
