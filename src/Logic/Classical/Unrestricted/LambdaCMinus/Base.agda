open import Function                              using (id; _∘_)
open import Data.Fin                              using (Fin; suc; zero; inject+)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable            using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])

module Logic.Classical.Unrestricted.LambdaCMinus.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Type                Univ renaming (_⇛_ to _-_)
open import Logic.Structure           Univ
open import Logic.Classical.Judgement Univ


infix 1 λC⁻_

data λC⁻_ : Judgement → Set ℓ where

  ax   : ∀ {Γ Δ} {{p₁ : True (Conjunction? Γ)}} {{p₂ : True (Disjunction? Δ)}}
       → (x : Fin _)
       → λC⁻                 Γ ⊢[ Γ ‼ x ]         Δ

  ⇒ᵢ   : ∀ {Γ A B Δ}
       → λC⁻         · A · ⊗ Γ ⊢[     B ]         Δ
       → λC⁻                 Γ ⊢[ A ⇒ B ]         Δ

  ⇒ₑ   : ∀ {Γ A B Δ}
       → λC⁻                 Γ ⊢[ A ⇒ B ]         Δ
       → λC⁻                 Γ ⊢[ A     ]         Δ
       → λC⁻                 Γ ⊢[     B ]         Δ

  raa  : ∀ {Γ A Δ}
       → λC⁻                 Γ ⊢          · A · ⊕ Δ
       → λC⁻                 Γ ⊢[ A     ]         Δ

  ⇒ₑᵏ  : ∀ {Γ Δ}
       → (α : Fin _)
       → λC⁻                 Γ ⊢[ Δ ‼ α ]         Δ
       → λC⁻                 Γ ⊢                  Δ

  -ᵢ   : ∀ {Γ A B Δ}
       → λC⁻                 Γ ⊢[ A     ]         Δ
       → λC⁻         · B · ⊗ Γ ⊢                  Δ
       → λC⁻                 Γ ⊢[ A - B ]         Δ

  -ₑ   : ∀ {Γ A B C Δ}
       → λC⁻                 Γ ⊢[ A - B ]         Δ
       → λC⁻         · A · ⊗ Γ ⊢[ C     ] · B · ⊕ Δ
       → λC⁻                 Γ ⊢[ C     ]         Δ

  ⊗ᵢ   : ∀ {Γ A B Δ}
       → λC⁻                 Γ ⊢[ A     ]         Δ
       → λC⁻                 Γ ⊢[     B ]         Δ
       → λC⁻                 Γ ⊢[ A ⊗ B ]         Δ

  ⊗ₑ   : ∀ {Γ A B C Δ}
       → λC⁻                 Γ ⊢[ A ⊗ B ]         Δ
       → λC⁻ · A · ⊗ · B · ⊗ Γ ⊢[ C     ]         Δ
       → λC⁻                 Γ ⊢[ C     ]         Δ


-- Proof: with the above axiomatisation, you are guaranteed to
-- maintain the context structures as a sequence of conjuctions and a
-- sequence of disjunctions.
structure : ∀ {J} (f : λC⁻ J) → Conjunction (⊢₁ J) × Disjunction (⊢₂ J)
structure (ax  {{p₁}} {{p₂}} x  ) = (toWitness p₁ , toWitness p₂)
structure (⇒ᵢ                f  ) = map (proj₂ ∘ ⊗⟶×) id (structure f)
structure (⇒ₑ                f g) = structure f
structure (raa               f  ) = map id (proj₂ ∘ ⊕⟶×) (structure f)
structure (⇒ₑᵏ               α f) = structure f
structure (-ᵢ                f g) = structure f
structure (-ₑ                f g) = structure f
structure (⊗ᵢ                f g) = structure f
structure (⊗ₑ                f g) = structure f


