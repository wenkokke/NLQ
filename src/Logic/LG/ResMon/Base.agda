------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.LG.ResMon.Base {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type             Atom
open import Logic.LG.ResMon.Judgement Atom


infix  1  LG_ _⊢LG_
infixl 50 _⋈ᵗ _∞ᵗ

mutual
  _⊢LG_ : Type → Type → Set ℓ
  A ⊢LG B = LG A ⊢ B

  data LG_ : Judgement → Set ℓ where

    ax  : ∀ {A}       → el A ⊢LG el A

    -- rules for residuation and monotonicity for (□ , ◇)
    m□  : ∀ {A B}     →   A ⊢LG   B → □ A ⊢LG □ B
    m◇  : ∀ {A B}     →   A ⊢LG   B → ◇ A ⊢LG ◇ B
    r□◇ : ∀ {A B}     →   A ⊢LG □ B → ◇ A ⊢LG   B
    r◇□ : ∀ {A B}     → ◇ A ⊢LG   B →   A ⊢LG □ B

    -- rules for residuation and monotonicity for (₀ , ⁰)
    m⁰  : ∀ {A B}     → B ⊢LG   A   →   A ⁰ ⊢LG   B ⁰
    m₀  : ∀ {A B}     → B ⊢LG   A   → ₀ A   ⊢LG ₀ B
    r⁰₀ : ∀ {A B}     → B ⊢LG   A ⁰ →   A   ⊢LG ₀ B
    r₀⁰ : ∀ {A B}     → B ⊢LG ₀ A   →   A   ⊢LG   B ⁰

    -- rules for residuation and monotonicity for (₁ , ¹)
    m₁  : ∀ {A B}     →   B   ⊢LG A → ₁ A   ⊢LG ₁ B
    m¹  : ∀ {A B}     →   B   ⊢LG A →   A ¹ ⊢LG   B ¹
    r¹₁ : ∀ {A B}     →   B ¹ ⊢LG A → ₁ A   ⊢LG   B
    r₁¹ : ∀ {A B}     → ₁ B   ⊢LG A →   A ¹ ⊢LG   B

    -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
    m⊗  : ∀ {A B C D} → A ⊢LG B     → C ⊢LG D     → A ⊗ C ⊢LG B ⊗ D
    m⇒  : ∀ {A B C D} → A ⊢LG B     → C ⊢LG D     → B ⇒ C ⊢LG A ⇒ D
    m⇐  : ∀ {A B C D} → A ⊢LG B     → C ⊢LG D     → A ⇐ D ⊢LG B ⇐ C
    r⇒⊗ : ∀ {A B C}   → B ⊢LG A ⇒ C → A ⊗ B ⊢LG C
    r⊗⇒ : ∀ {A B C}   → A ⊗ B ⊢LG C → B ⊢LG A ⇒ C
    r⇐⊗ : ∀ {A B C}   → A ⊢LG C ⇐ B → A ⊗ B ⊢LG C
    r⊗⇐ : ∀ {A B C}   → A ⊗ B ⊢LG C → A ⊢LG C ⇐ B

    -- rules for residuation and monotonicity for (⇚ , ⊕ , ⇛)
    m⊕  : ∀ {A B C D} → A ⊢LG B     → C ⊢LG D     → A ⊕ C ⊢LG B ⊕ D
    m⇛  : ∀ {A B C D} → C ⊢LG D     → A ⊢LG B     → D ⇛ A ⊢LG C ⇛ B
    m⇚  : ∀ {A B C D} → A ⊢LG B     → C ⊢LG D     → A ⇚ D ⊢LG B ⇚ C
    r⇛⊕ : ∀ {A B C}   → B ⇛ C ⊢LG A → C ⊢LG B ⊕ A
    r⊕⇛ : ∀ {A B C}   → C ⊢LG B ⊕ A → B ⇛ C ⊢LG A
    r⊕⇚ : ∀ {A B C}   → C ⊢LG B ⊕ A → C ⇚ A ⊢LG B
    r⇚⊕ : ∀ {A B C}   → C ⇚ A ⊢LG B → C ⊢LG B ⊕ A

    -- grishin distributives
    d⇛⇐ : ∀ {A B C D} → A ⊗ B ⊢LG C ⊕ D → C ⇛ A ⊢LG D ⇐ B
    d⇛⇒ : ∀ {A B C D} → A ⊗ B ⊢LG C ⊕ D → C ⇛ B ⊢LG A ⇒ D
    d⇚⇒ : ∀ {A B C D} → A ⊗ B ⊢LG C ⊕ D → B ⇚ D ⊢LG A ⇒ C
    d⇚⇐ : ∀ {A B C D} → A ⊗ B ⊢LG C ⊕ D → A ⇚ D ⊢LG C ⇐ B


-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `LG`.
ax′ : ∀ {A} → A ⊢LG A
ax′ {el A}  = ax
ax′ {□  A}  = m□ ax′
ax′ {◇  A}  = m◇ ax′
ax′ {₀  A}  = m₀ ax′
ax′ {A  ⁰}  = m⁰ ax′
ax′ {₁  A}  = m₁ ax′
ax′ {A  ¹}  = m¹ ax′
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇚ B} = m⇚ ax′ ax′
ax′ {A ⇛ B} = m⇛ ax′ ax′
ax′ {A ⊕ B} = m⊕ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′

-- Derived rules for two-step residuations.
r⇐⇒′ : ∀ {A B C} → A ⊢LG C ⇐ B → B ⊢LG A ⇒ C
r⇐⇒′ = r⊗⇒ ∘ r⇐⊗
r⇒⇐′ : ∀ {A B C} → B ⊢LG A ⇒ C → A ⊢LG C ⇐ B
r⇒⇐′ = r⊗⇐ ∘ r⇒⊗

-- Derived rules for two-step co-residuations.
r⇚⇛′ : ∀ {A B C} → C ⇚ A ⊢LG B → B ⇛ C ⊢LG A
r⇚⇛′ = r⊕⇛ ∘ r⇚⊕
r⇛⇚′ : ∀ {A B C} → B ⇛ C ⊢LG A → C ⇚ A ⊢LG B
r⇛⇚′ = r⊕⇚ ∘ r⇛⊕

-- Derived rules for application.
appl-⇒′ : ∀ {A B C} → B ⊢LG C → A ⊗ (A ⇒ B) ⊢LG C
appl-⇒′ f = r⇒⊗ (m⇒ ax′ f)
appl-⇐′ : ∀ {A B C} → B ⊢LG C → (B ⇐ A) ⊗ A ⊢LG C
appl-⇐′ f = r⇐⊗ (m⇐ f ax′)

-- Derived rules for co-application.
appl-⇛′ : ∀ {A B C} → B ⊢LG C → B ⊢LG A ⊕ (A ⇛ C)
appl-⇛′ f = r⇛⊕ (m⇛ ax′ f)
appl-⇚′ : ∀ {A B C} → B ⊢LG C → B ⊢LG (C ⇚ A) ⊕ A
appl-⇚′ f = r⇚⊕ (m⇚ f ax′)


-- Symmetries that do hold
_⋈ᵗ : ∀ {J} → LG J → LG (J ⋈ʲ)
_⋈ᵗ  ax       = ax
_⋈ᵗ (m□  f  ) = m□  (f ⋈ᵗ)
_⋈ᵗ (m◇  f  ) = m◇  (f ⋈ᵗ)
_⋈ᵗ (r□◇ f  ) = r□◇ (f ⋈ᵗ)
_⋈ᵗ (r◇□ f  ) = r◇□ (f ⋈ᵗ)
_⋈ᵗ (m⁰  f  ) = m₀  (f ⋈ᵗ)
_⋈ᵗ (m₀  f  ) = m⁰  (f ⋈ᵗ)
_⋈ᵗ (r⁰₀ f  ) = r₀⁰ (f ⋈ᵗ)
_⋈ᵗ (r₀⁰ f  ) = r⁰₀ (f ⋈ᵗ)
_⋈ᵗ (m₁  f  ) = m¹  (f ⋈ᵗ)
_⋈ᵗ (m¹  f  ) = m₁  (f ⋈ᵗ)
_⋈ᵗ (r¹₁ f  ) = r₁¹ (f ⋈ᵗ)
_⋈ᵗ (r₁¹ f  ) = r¹₁ (f ⋈ᵗ)
_⋈ᵗ (m⊗  f g) = m⊗  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (m⇒  f g) = m⇐  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (m⇐  f g) = m⇒  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (r⇒⊗ f  ) = r⇐⊗ (f ⋈ᵗ)
_⋈ᵗ (r⊗⇒ f  ) = r⊗⇐ (f ⋈ᵗ)
_⋈ᵗ (r⇐⊗ f  ) = r⇒⊗ (f ⋈ᵗ)
_⋈ᵗ (r⊗⇐ f  ) = r⊗⇒ (f ⋈ᵗ)
_⋈ᵗ (m⊕  f g) = m⊕  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (m⇛  f g) = m⇚  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (m⇚  f g) = m⇛  (g ⋈ᵗ) (f ⋈ᵗ)
_⋈ᵗ (r⇛⊕ f  ) = r⇚⊕ (f ⋈ᵗ)
_⋈ᵗ (r⊕⇛ f  ) = r⊕⇚ (f ⋈ᵗ)
_⋈ᵗ (r⊕⇚ f  ) = r⊕⇛ (f ⋈ᵗ)
_⋈ᵗ (r⇚⊕ f  ) = r⇛⊕ (f ⋈ᵗ)
_⋈ᵗ (d⇛⇐ f  ) = d⇚⇒ (f ⋈ᵗ)
_⋈ᵗ (d⇛⇒ f  ) = d⇚⇐ (f ⋈ᵗ)
_⋈ᵗ (d⇚⇒ f  ) = d⇛⇐ (f ⋈ᵗ)
_⋈ᵗ (d⇚⇐ f  ) = d⇛⇒ (f ⋈ᵗ)


_∞ᵗ : ∀ {J} → LG J → LG (J ∞ʲ)
_∞ᵗ  ax       = ax
_∞ᵗ (m□  f  ) = m◇  (f ∞ᵗ)
_∞ᵗ (m◇  f  ) = m□  (f ∞ᵗ)
_∞ᵗ (r□◇ f  ) = r◇□ (f ∞ᵗ)
_∞ᵗ (r◇□ f  ) = r□◇ (f ∞ᵗ)
_∞ᵗ (m⁰  f  ) = m₁  (f ∞ᵗ)
_∞ᵗ (m₀  f  ) = m¹  (f ∞ᵗ)
_∞ᵗ (r⁰₀ f  ) = r₁¹ (f ∞ᵗ)
_∞ᵗ (r₀⁰ f  ) = r¹₁ (f ∞ᵗ)
_∞ᵗ (m₁  f  ) = m⁰  (f ∞ᵗ)
_∞ᵗ (m¹  f  ) = m₀  (f ∞ᵗ)
_∞ᵗ (r¹₁ f  ) = r₀⁰ (f ∞ᵗ)
_∞ᵗ (r₁¹ f  ) = r⁰₀ (f ∞ᵗ)
_∞ᵗ (m⊗  f g) = m⊕  (g ∞ᵗ) (f ∞ᵗ)
_∞ᵗ (m⇒  f g) = m⇚  (g ∞ᵗ) (f ∞ᵗ)
_∞ᵗ (m⇐  f g) = m⇛  (g ∞ᵗ) (f ∞ᵗ)
_∞ᵗ (r⇒⊗ f  ) = r⇚⊕ (f ∞ᵗ)
_∞ᵗ (r⊗⇒ f  ) = r⊕⇚ (f ∞ᵗ)
_∞ᵗ (r⇐⊗ f  ) = r⇛⊕ (f ∞ᵗ)
_∞ᵗ (r⊗⇐ f  ) = r⊕⇛ (f ∞ᵗ)
_∞ᵗ (m⊕  f g) = m⊗  (g ∞ᵗ) (f ∞ᵗ)
_∞ᵗ (m⇛  f g) = m⇐  (g ∞ᵗ) (f ∞ᵗ)
_∞ᵗ (m⇚  f g) = m⇒  (g ∞ᵗ) (f ∞ᵗ)
_∞ᵗ (r⇛⊕ f  ) = r⇐⊗ (f ∞ᵗ)
_∞ᵗ (r⊕⇛ f  ) = r⊗⇐ (f ∞ᵗ)
_∞ᵗ (r⊕⇚ f  ) = r⊗⇒ (f ∞ᵗ)
_∞ᵗ (r⇚⊕ f  ) = r⇒⊗ (f ∞ᵗ)
_∞ᵗ (d⇛⇐ f  ) = d⇛⇐ (f ∞ᵗ)
_∞ᵗ (d⇛⇒ f  ) = d⇚⇐ (f ∞ᵗ)
_∞ᵗ (d⇚⇒ f  ) = d⇚⇒ (f ∞ᵗ)
_∞ᵗ (d⇚⇐ f  ) = d⇛⇒ (f ∞ᵗ)


_⋈ᵗ⁻¹ : ∀ {J} → LG (J ⋈ʲ) → LG J
_⋈ᵗ⁻¹ {J} f = P.subst LG_ (⋈ʲ-inv J) (f ⋈ᵗ)


_∞ᵗ⁻¹ : ∀ {J} → LG (J ∞ʲ) → LG J
_∞ᵗ⁻¹ {J} f = P.subst LG_ (∞ʲ-inv J) (f ∞ᵗ)


infix 5 is-ax_ is-ax?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-ax_ : ∀ {A B} (f : A ⊢LG B) → Set ℓ
is-ax_ f = ∃ (λ A → f ≅ ax {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-ax?_ : ∀ {A B} (f : A ⊢LG B) → Dec (is-ax f)
is-ax? ax      = yes (_ , H.refl)
is-ax? m□  _   = no (λ {(_ , ())})
is-ax? m◇  _   = no (λ {(_ , ())})
is-ax? r□◇ _   = no (λ {(_ , ())})
is-ax? r◇□ _   = no (λ {(_ , ())})
is-ax? m⁰  _   = no (λ {(_ , ())})
is-ax? m₀  _   = no (λ {(_ , ())})
is-ax? r⁰₀ _   = no (λ {(_ , ())})
is-ax? r₀⁰ _   = no (λ {(_ , ())})
is-ax? m₁  _   = no (λ {(_ , ())})
is-ax? m¹  _   = no (λ {(_ , ())})
is-ax? r¹₁ _   = no (λ {(_ , ())})
is-ax? r₁¹ _   = no (λ {(_ , ())})
is-ax? m⊗  _ _ = no (λ {(_ , ())})
is-ax? m⇒  _ _ = no (λ {(_ , ())})
is-ax? m⇐  _ _ = no (λ {(_ , ())})
is-ax? r⇒⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇒ _   = no (λ {(_ , ())})
is-ax? r⇐⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇐ _   = no (λ {(_ , ())})
is-ax? r⇛⊕ _   = no (λ {(_ , ())})
is-ax? r⊕⇛ _   = no (λ {(_ , ())})
is-ax? r⊕⇚ _   = no (λ {(_ , ())})
is-ax? r⇚⊕ _   = no (λ {(_ , ())})
is-ax? m⊕  _ _ = no (λ {(_ , ())})
is-ax? m⇛  _ _ = no (λ {(_ , ())})
is-ax? m⇚  _ _ = no (λ {(_ , ())})
is-ax? d⇛⇐ _   = no (λ {(_ , ())})
is-ax? d⇛⇒ _   = no (λ {(_ , ())})
is-ax? d⇚⇒ _   = no (λ {(_ , ())})
is-ax? d⇚⇐ _   = no (λ {(_ , ())})
