------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Function                                        using (_∘_)
open import Data.Product                                    using (∃; _×_; _,_)
open import Data.Sum                                        using (inj₁; inj₂)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness; fromWitness)
open import Relation.Binary                                 using (Rel)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)


module Logic.Classical.Unrestricted.LambekGrishin.BooleanAlgebra {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity

PolarisedUniv : Set ℓ
PolarisedUniv = (Polarity × Univ)

open import Logic.Classical.Unrestricted.LambekGrishin.Type                PolarisedUniv
open import Logic.Classical.Unrestricted.LambekGrishin.Structure.Polarised PolarisedUniv
open import Logic.Classical.Unrestricted.LambekGrishin.Judgement           PolarisedUniv
open import Logic.Classical.Unrestricted.LambekGrishin.Type.Polarised      Univ
open import Logic.Classical.Unrestricted.LambekGrishin.Base                Univ

_≤_ : Rel Type ℓ
A ≤ B = LG · A · ⊢ · B ·

refl : ∀ {A} → A ≤ A
refl {A} with Polarity? A
refl | inj₁ A⁺ = ⇀ {p = fromWitness A⁺} ax⁺
refl | inj₂ A⁻ = ↼ {p = fromWitness A⁻} ax⁻

postulate
  trans : ∀ {A B C} → A ≤ B → B ≤ C → A ≤ C

open import Relation.Binary.PartialOrderToEquivalence _≤_ refl trans renaming (_≈_ to _⊣⊢_)

private
  ∨-comm      : ∀ {A B} → A ⊕ B ≤ B ⊕ A
  ∨-comm      = ⊕ᴿ (⊕⃡ (↼ (⊕ᴸ ax⁻ ax⁻)))
  ∨-assoc₁    : ∀ {A B C} → (A ⊕ B) ⊕ C ≤ A ⊕ (B ⊕ C)
  ∨-assoc₁    = ⊕ᴿ (r⇛⊕′ (⊕ᴿ (r⊕⇛′ (⊕⃔ (↼ (⊕ᴸ (⊕ᴸ ax⁻ ax⁻) ax⁻))))))
  ∨-assoc₂    : ∀ {A B C} → A ⊕ (B ⊕ C) ≤ (A ⊕ B) ⊕ C
  ∨-assoc₂    = ⊕ᴿ (r⇚⊕  (⊕ᴿ (r⊕⇚  (⊕⃕ (↼ (⊕ᴸ ax⁻ (⊕ᴸ ax⁻ ax⁻)))))))
  ∧-comm      : ∀ {A B} → A ⊗ B ≤ B ⊗ A
  ∧-comm      = ⊗ᴸ (⊗⃡ (⇀ (⊗ᴿ ax⁺ ax⁺)))
  ∧-assoc₁    : ∀ {A B C} → (A ⊗ B) ⊗ C ≤ A ⊗ (B ⊗ C)
  ∧-assoc₁    = ⊗ᴸ (r⇐⊗′ (⊗ᴸ (r⊗⇐′ (⊗⃕ (⇀ (⊗ᴿ ax⁺ (⊗ᴿ ax⁺ ax⁺)))))))
  ∧-assoc₂    : ∀ {A B C} → A ⊗ (B ⊗ C) ≤ (A ⊗ B) ⊗ C
  ∧-assoc₂    = ⊗ᴸ (r⇒⊗  (⊗ᴸ (r⊗⇒  (⊗⃔ (⇀ (⊗ᴿ (⊗ᴿ ax⁺ ax⁺) ax⁺))))))
  absorptive₁ : ∀ {A B} → A ⊕ A ⊗ B ≤ A
  absorptive₁ = ⊕ᶜ (↼ (⊕ᴸ ax⁻ (↽ (⊗ᴸ (⊗ʷ refl)))))
  absorptive₂ : ∀ {A B} → A ≤ A ⊕ A ⊗ B
  absorptive₂ = ⊕ᴿ (⊕ʷ refl)
  absorptive₃ : ∀ {A B} → A ⊗ A ⊕ B ≤ A
  absorptive₃ = ⊗ᴸ (⊗ʷ refl)
  absorptive₄ : ∀ {A B} → A ≤ A ⊗ A ⊕ B
  absorptive₄ = ⊗ᶜ (⇀ (⊗ᴿ ax⁺ (⇁ (⊕ᴿ (⊕ʷ refl)))))



isLattice : IsLattice _⊣⊢_ _⊕_ _⊗_
isLattice = record
  { isEquivalence = isEquivalence
  ; ∨-comm        = λ _ _   → ∨-comm   , ∨-comm
  ; ∨-assoc       = λ _ _ _ → ∨-assoc₁ , ∨-assoc₂
  ; ∨-cong        = {!!}
  ; ∧-comm        = λ _ _   → ∧-comm   , ∧-comm
  ; ∧-assoc       = λ _ _ _ → ∧-assoc₁ , ∧-assoc₂
  ; ∧-cong        = {!!}
  ; absorptive    = (λ _ _ → absorptive₁ , absorptive₂)
                  , (λ _ _ → absorptive₃ , absorptive₄)
  }


lattice : Lattice ℓ _
lattice = record
  { Carrier   = Type
  ; _≈_       = _≡_
  ; _∨_       = _⊕_
  ; _∧_       = _⊗_
  ; isLattice = {!!}
  }
