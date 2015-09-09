--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Base.agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.NLP.ResMon.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.Type             Atom
open import Logic.NLP.ResMon.Sequent Atom


infix  1  NLP_ _⊢NLP_
mutual
  _⊢NLP_ : Type → Type → Set ℓ
  A ⊢NLP B = NLP A ⊢ B

  data NLP_ : Sequent → Set ℓ where

    ax  : ∀ {A}       → el A ⊢NLP el A

    -- rules for residuation and monotonicity for (□ , ◇)
    m□  : ∀ {A B}     →   A ⊢NLP   B → □ A ⊢NLP □ B
    m◇  : ∀ {A B}     →   A ⊢NLP   B → ◇ A ⊢NLP ◇ B
    r□◇ : ∀ {A B}     →   A ⊢NLP □ B → ◇ A ⊢NLP   B
    r◇□ : ∀ {A B}     → ◇ A ⊢NLP   B →   A ⊢NLP □ B

    -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
    m⊗  : ∀ {A B C D} → A ⊢NLP B     → C ⊢NLP D     → A ⊗ C ⊢NLP B ⊗ D
    m⇒  : ∀ {A B C D} → A ⊢NLP B     → C ⊢NLP D     → B ⇒ C ⊢NLP A ⇒ D
    m⇐  : ∀ {A B C D} → A ⊢NLP B     → C ⊢NLP D     → A ⇐ D ⊢NLP B ⇐ C
    r⇒⊗ : ∀ {A B C}   → B ⊢NLP A ⇒ C → A ⊗ B ⊢NLP C
    r⊗⇒ : ∀ {A B C}   → A ⊗ B ⊢NLP C → B ⊢NLP A ⇒ C
    r⇐⊗ : ∀ {A B C}   → A ⊢NLP C ⇐ B → A ⊗ B ⊢NLP C
    r⊗⇐ : ∀ {A B C}   → A ⊗ B ⊢NLP C → A ⊢NLP C ⇐ B

    -- structural postulates for extraction/infixation
    p1  : ∀ {A B C D} → (A ⊗ B) ⊗ ◇ C ⊢NLP D → A ⊗ (B ⊗ ◇ C) ⊢NLP D
    p2  : ∀ {A B C D} → (A ⊗ B) ⊗ ◇ C ⊢NLP D → (A ⊗ ◇ C) ⊗ B ⊢NLP D
    p1′ : ∀ {A B C D} → ◇ C ⊗ (B ⊗ A) ⊢NLP D → (◇ C ⊗ B) ⊗ A ⊢NLP D
    p2′ : ∀ {A B C D} → ◇ C ⊗ (B ⊗ A) ⊢NLP D → B ⊗ (◇ C ⊗ A) ⊢NLP D

-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `NLP`.
ax′ : ∀ {A} → A ⊢NLP A
ax′ {el A}  = ax
ax′ {□  A}  = m□ ax′
ax′ {◇  A}  = m◇ ax′
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′

-- Derived rules for two-step residuations.
r⇐⇒′ : ∀ {A B C} → A ⊢NLP C ⇐ B → B ⊢NLP A ⇒ C
r⇐⇒′ = r⊗⇒ ∘ r⇐⊗
r⇒⇐′ : ∀ {A B C} → B ⊢NLP A ⇒ C → A ⊢NLP C ⇐ B
r⇒⇐′ = r⊗⇐ ∘ r⇒⊗

-- Derived rules for application.
appl-⇒′ : ∀ {A B C} → B ⊢NLP C → A ⊗ (A ⇒ B) ⊢NLP C
appl-⇒′ f = r⇒⊗ (m⇒ ax′ f)
appl-⇐′ : ∀ {A B C} → B ⊢NLP C → (B ⇐ A) ⊗ A ⊢NLP C
appl-⇐′ f = r⇐⊗ (m⇐ f ax′)


-- Symmetries that do hold
_⋈ᵗ : ∀ {J} → NLP J → NLP (J ⋈ʲ)
_⋈ᵗ  ax       = ax
_⋈ᵗ (m□  f  ) = m□  (f ⋈ᵗ)
_⋈ᵗ (m◇  f  ) = m◇  (f ⋈ᵗ)
_⋈ᵗ (r□◇ f  ) = r□◇ (f ⋈ᵗ)
_⋈ᵗ (r◇□ f  ) = r◇□ (f ⋈ᵗ)
_⋈ᵗ (m⊗  f g) = m⊗  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (m⇒  f g) = m⇐  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (m⇐  f g) = m⇒  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (r⇒⊗ f  ) = r⇐⊗ (f ⋈ᵗ)
_⋈ᵗ (r⊗⇒ f  ) = r⊗⇐ (f ⋈ᵗ)
_⋈ᵗ (r⇐⊗ f  ) = r⇒⊗ (f ⋈ᵗ)
_⋈ᵗ (r⊗⇐ f  ) = r⊗⇒ (f ⋈ᵗ)
_⋈ᵗ (p1  f  ) = p1′ (f ⋈ᵗ)
_⋈ᵗ (p2  f  ) = p2′ (f ⋈ᵗ)
_⋈ᵗ (p1′ f  ) = p1  (f ⋈ᵗ)
_⋈ᵗ (p2′ f  ) = p2  (f ⋈ᵗ)


_⋈ᵗ⁻¹ : ∀ {J} → NLP (J ⋈ʲ) → NLP J
_⋈ᵗ⁻¹ {J} f = P.subst NLP_ (⋈ʲ-inv J) (f ⋈ᵗ)



infix 5 is-ax_ is-ax?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-ax_ : ∀ {A B} (f : A ⊢NLP B) → Set ℓ
is-ax_ f = ∃ (λ A → f ≅ ax {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-ax?_ : ∀ {A B} (f : A ⊢NLP B) → Dec (is-ax f)
is-ax? ax      = yes (_ , H.refl)
is-ax? m□  _   = no (λ {(_ , ())})
is-ax? m◇  _   = no (λ {(_ , ())})
is-ax? r□◇ _   = no (λ {(_ , ())})
is-ax? r◇□ _   = no (λ {(_ , ())})
is-ax? m⊗  _ _ = no (λ {(_ , ())})
is-ax? m⇒  _ _ = no (λ {(_ , ())})
is-ax? m⇐  _ _ = no (λ {(_ , ())})
is-ax? r⇒⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇒ _   = no (λ {(_ , ())})
is-ax? r⇐⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇐ _   = no (λ {(_ , ())})
is-ax? p1  _   = no (λ {(_ , ())})
is-ax? p2  _   = no (λ {(_ , ())})
is-ax? p1′ _   = no (λ {(_ , ())})
is-ax? p2′ _   = no (λ {(_ , ())})


-- -}
-- -}
-- -}
-- -}
-- -}
