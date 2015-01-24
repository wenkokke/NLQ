open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Fin                              using (Fin; suc; zero)
open import Data.List                             using (List; _∷_; []; _++_; length)
open import Data.List.Properties                  using (length-++)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


module Logic.Structure {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ


data Structure : Set ℓ where

  ·_· : Type → Structure
  
  _⇒_ : Structure → Structure → Structure
  _⇐_ : Structure → Structure → Structure

  _⇚_ : Structure → Structure → Structure
  _⇛_ : Structure → Structure → Structure

  _⊗_ : Structure → Structure → Structure
  _⊕_ : Structure → Structure → Structure


data Conjunction : Structure → Set ℓ where

  ·_· : (A : Type) → Conjunction (· A ·)
  _⊗_ : {Γ Δ : Structure} → Conjunction Γ → Conjunction Δ → Conjunction (Γ ⊗ Δ)


⊗⟶× : ∀ {Γ Δ} → Conjunction (Γ ⊗ Δ) → Conjunction Γ × Conjunction Δ
⊗⟶× (p₁ ⊗ p₂) = (p₁ , p₂)


Conjunction? : (Γ : Structure) → Dec (Conjunction Γ)
Conjunction? (· A ·) = yes · A ·
Conjunction? (Γ ⇒ Δ) = no (λ ())
Conjunction? (Γ ⇐ Δ) = no (λ ())
Conjunction? (Γ ⇚ Δ) = no (λ ())
Conjunction? (Γ ⇛ Δ) = no (λ ())
Conjunction? (Γ ⊗ Δ) with Conjunction? Γ | Conjunction? Δ
Conjunction? (Γ ⊗ Δ) | yes p₁ | yes p₂ = yes (p₁ ⊗ p₂)
Conjunction? (Γ ⊗ Δ) | no ¬p₁ | _      = no (λ {(p₁ ⊗ _ ) → ¬p₁ p₁})
Conjunction? (Γ ⊗ Δ) | _      | no ¬p₂ = no (λ {(_  ⊗ p₂) → ¬p₂ p₂})
Conjunction? (Γ ⊕ Δ) = no (λ ())


data Disjunction : Structure → Set ℓ where

  ·_· : (A : Type) → Disjunction  (· A ·)
  _⊕_ : {Γ Δ : Structure} → Disjunction  Γ → Disjunction  Δ → Disjunction  (Γ ⊕ Δ)


Disjunction? : (Γ : Structure) → Dec (Disjunction Γ)
Disjunction? (· A ·) = yes · A ·
Disjunction? (Γ ⇒ Δ) = no (λ ())
Disjunction? (Γ ⇐ Δ) = no (λ ())
Disjunction? (Γ ⇚ Δ) = no (λ ())
Disjunction? (Γ ⇛ Δ) = no (λ ())
Disjunction? (Γ ⊗ Δ) = no (λ ())
Disjunction? (Γ ⊕ Δ) with Disjunction? Γ | Disjunction? Δ
Disjunction? (Γ ⊕ Δ) | yes p₁ | yes p₂ = yes (p₁ ⊕ p₂)
Disjunction? (Γ ⊕ Δ) | no ¬p₁ | _      = no (λ {(p₁ ⊕ _ ) → ¬p₁ p₁})
Disjunction? (Γ ⊕ Δ) | _      | no ¬p₂ = no (λ {(_  ⊕ p₂) → ¬p₂ p₂})


⊕⟶× : ∀ {Γ Δ} → Disjunction (Γ ⊕ Δ) → Disjunction Γ × Disjunction Δ
⊕⟶× (p₁ ⊕ p₂) = (p₁ , p₂)


size : Structure → ℕ
size (· _ ·) = 1
size (Γ ⇒ Δ) = size Γ + size Δ
size (Γ ⇐ Δ) = size Γ + size Δ
size (Γ ⇚ Δ) = size Γ + size Δ
size (Γ ⇛ Δ) = size Γ + size Δ
size (Γ ⊗ Δ) = size Γ + size Δ
size (Γ ⊕ Δ) = size Γ + size Δ


break : ∀ {m n} → Fin (m + n) → Fin m ⊎ Fin n
break {zero}   x      = inj₂ x
break {suc m}  zero   = inj₁ zero
break {suc m} (suc x) with break {m} x
break {suc m} (suc _) | inj₁ x = inj₁ (suc x)
break {suc m} (suc _) | inj₂ y = inj₂ y


_‼_ : (Γ : Structure) (x : Fin (size Γ)) → Type
(· A ·) ‼ zero = A
(· A ·) ‼ suc ()
(Γ ⇒ Δ) ‼ x with break x
(Γ ⇒ Δ) ‼ _ | inj₁ x = Γ ‼ x
(Γ ⇒ Δ) ‼ _ | inj₂ y = Δ ‼ y
(Γ ⇐ Δ) ‼ x with break x
(Γ ⇐ Δ) ‼ _ | inj₁ x = Γ ‼ x
(Γ ⇐ Δ) ‼ _ | inj₂ y = Δ ‼ y
(Γ ⇚ Δ) ‼ x with break x
(Γ ⇚ Δ) ‼ _ | inj₁ x = Γ ‼ x
(Γ ⇚ Δ) ‼ _ | inj₂ y = Δ ‼ y
(Γ ⇛ Δ) ‼ x with break x
(Γ ⇛ Δ) ‼ _ | inj₁ x = Γ ‼ x
(Γ ⇛ Δ) ‼ _ | inj₂ y = Δ ‼ y
(Γ ⊗ Δ) ‼ x with break x
(Γ ⊗ Δ) ‼ _ | inj₁ x = Γ ‼ x
(Γ ⊗ Δ) ‼ _ | inj₂ y = Δ ‼ y
(Γ ⊕ Δ) ‼ x with break x
(Γ ⊕ Δ) ‼ _ | inj₁ x = Γ ‼ x
(Γ ⊕ Δ) ‼ _ | inj₂ y = Δ ‼ y
