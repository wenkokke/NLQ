--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.MM96.ResMon.Base {ℓ} (Atom : Set ℓ) where


open import Logic.MM96.Type             Atom
open import Logic.MM96.ResMon.Judgement Atom


infix  1  MM96_

data MM96_ : Judgement → Set ℓ where

  ax   : ∀ {A}       → MM96 el A ⊢ el A

  -- rules for monotonicity for (⟨t⟩ , ⟨l⟩ , ⟨r⟩)
  m⟨t⟩ :               MM96 ⟨t⟩ ⊢ ⟨t⟩
  m⟨l⟩ : ∀ {A B}     → MM96 A ⊢ B → MM96 ⟨l⟩ A ⊢ ⟨l⟩ B
  m⟨r⟩ : ∀ {A B}     → MM96 A ⊢ B → MM96 ⟨r⟩ A ⊢ ⟨r⟩ B

  -- rules for residuation and monotonicity for (◇ , □)
  m◇   : ∀ {A B}     → MM96   A ⊢   B → MM96 ◇ A ⊢ ◇ B
  m□   : ∀ {A B}     → MM96   A ⊢   B → MM96 □ A ⊢ □ B
  r□◇  : ∀ {A B}     → MM96   A ⊢ □ B → MM96 ◇ A ⊢   B
  r◇□  : ∀ {A B}     → MM96 ◇ A ⊢   B → MM96   A ⊢ □ B

  -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
  m⊗   : ∀ {A B C D} → MM96 A ⊢ B     → MM96 C ⊢ D     → MM96 A ⊗ C ⊢ B ⊗ D
  m⇒   : ∀ {A B C D} → MM96 A ⊢ B     → MM96 C ⊢ D     → MM96 B ⇒ C ⊢ A ⇒ D
  m⇐   : ∀ {A B C D} → MM96 A ⊢ B     → MM96 C ⊢ D     → MM96 A ⇐ D ⊢ B ⇐ C
  r⇒⊗  : ∀ {A B C}   → MM96 B ⊢ A ⇒ C → MM96 A ⊗ B ⊢ C
  r⊗⇒  : ∀ {A B C}   → MM96 A ⊗ B ⊢ C → MM96 B ⊢ A ⇒ C
  r⇐⊗  : ∀ {A B C}   → MM96 A ⊢ C ⇐ B → MM96 A ⊗ B ⊢ C
  r⊗⇐  : ∀ {A B C}   → MM96 A ⊗ B ⊢ C → MM96 A ⊢ C ⇐ B

  -- rules for residuation and monotonicity for (⇦ , ⊙ , ⇨)
  m⊙   : ∀ {A B C D} → MM96 A ⊢ B     → MM96 C ⊢ D     → MM96 A ⊙ C ⊢ B ⊙ D
  m⇨   : ∀ {A B C D} → MM96 A ⊢ B     → MM96 C ⊢ D     → MM96 B ⇨ C ⊢ A ⇨ D
  m⇦   : ∀ {A B C D} → MM96 A ⊢ B     → MM96 C ⊢ D     → MM96 A ⇦ D ⊢ B ⇦ C
  r⇨⊙  : ∀ {A B C}   → MM96 B ⊢ A ⇨ C → MM96 A ⊙ B ⊢ C
  r⊙⇨  : ∀ {A B C}   → MM96 A ⊙ B ⊢ C → MM96 B ⊢ A ⇨ C
  r⇦⊙  : ∀ {A B C}   → MM96 A ⊢ C ⇦ B → MM96 A ⊙ B ⊢ C
  r⊙⇦  : ∀ {A B C}   → MM96 A ⊙ B ⊢ C → MM96 A ⊢ C ⇦ B

  -- rules for scope taking
  p₀   : ∀ {A B}     → MM96 ◇ A ⊢ B             → MM96 A ⊙ ⟨t⟩ ⊢ B
  p₀′  : ∀ {A B}     → MM96 A ⊙ ⟨t⟩ ⊢ B           → MM96 ◇ A ⊢ B
  p₁   : ∀ {A B C D} → MM96 (A ⊙ B) ⊗ C ⊢ D     → MM96 A ⊙ ⟨l⟩ (B ⊗ C) ⊢ D
  p₁′  : ∀ {A B C D} → MM96 A ⊙ ⟨l⟩ (B ⊗ C) ⊢ D → MM96 (A ⊙ B) ⊗ C ⊢ D
  p₂   : ∀ {A B C D} → MM96 A ⊗ (B ⊙ C) ⊢ D     → MM96 B ⊙ ⟨r⟩ (A ⊗ C) ⊢ D
  p₂′  : ∀ {A B C D} → MM96 B ⊙ ⟨r⟩ (A ⊗ C) ⊢ D → MM96 A ⊗ (B ⊙ C) ⊢ D


-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `MM96`.
ax′ : ∀ {A} → MM96 A ⊢ A
ax′ {el  A} = ax
ax′ {◇   A} = m◇ ax′
ax′ {□   A} = m□ ax′
ax′ {⟨t⟩  } = m⟨t⟩
ax′ {⟨l⟩ A} = m⟨l⟩ ax′
ax′ {⟨r⟩ A} = m⟨r⟩ ax′
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇦ B} = m⇦ ax′ ax′
ax′ {A ⇨ B} = m⇨ ax′ ax′
ax′ {A ⊙ B} = m⊙ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′

-- Derived rules for two-step residuations.
r⇐⇒′ : ∀ {A B C} → MM96 A ⊢ C ⇐ B → MM96 B ⊢ A ⇒ C
r⇐⇒′ = r⊗⇒ ∘ r⇐⊗
r⇒⇐′ : ∀ {A B C} → MM96 B ⊢ A ⇒ C → MM96 A ⊢ C ⇐ B
r⇒⇐′ = r⊗⇐ ∘ r⇒⊗

-- Derived rules for two-step co-residuations.
r⇦⇨′ : ∀ {A B C} → MM96 A ⊢ C ⇦ B → MM96 B ⊢ A ⇨ C
r⇦⇨′ = r⊙⇨ ∘ r⇦⊙
r⇨⇦′ : ∀ {A B C} → MM96 B ⊢ A ⇨ C → MM96 A ⊢ C ⇦ B
r⇨⇦′ = r⊙⇦ ∘ r⇨⊙


infix 5 is-ax_ is-ax?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-ax_ : ∀ {A B} (f : MM96 A ⊢ B) → Set ℓ
is-ax_ f = ∃ (λ A → f ≅ ax {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-ax?_ : ∀ {A B} (f : MM96 A ⊢ B) → Dec (is-ax f)
is-ax? ax      = yes (_ , H.refl)
is-ax? m⟨t⟩    = no (λ {(_ , ())})
is-ax? m⟨l⟩  _ = no (λ {(_ , ())})
is-ax? m⟨r⟩  _ = no (λ {(_ , ())})
is-ax? m◇    _ = no (λ {(_ , ())})
is-ax? m□    _ = no (λ {(_ , ())})
is-ax? r□◇ _   = no (λ {(_ , ())})
is-ax? r◇□ _   = no (λ {(_ , ())})
is-ax? m⊗  _ _ = no (λ {(_ , ())})
is-ax? m⇒  _ _ = no (λ {(_ , ())})
is-ax? m⇐  _ _ = no (λ {(_ , ())})
is-ax? r⇒⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇒ _   = no (λ {(_ , ())})
is-ax? r⇐⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇐ _   = no (λ {(_ , ())})
is-ax? r⇨⊙ _   = no (λ {(_ , ())})
is-ax? r⊙⇨ _   = no (λ {(_ , ())})
is-ax? r⊙⇦ _   = no (λ {(_ , ())})
is-ax? r⇦⊙ _   = no (λ {(_ , ())})
is-ax? m⊙  _ _ = no (λ {(_ , ())})
is-ax? m⇨  _ _ = no (λ {(_ , ())})
is-ax? m⇦  _ _ = no (λ {(_ , ())})
is-ax? p₀    _ = no (λ {(_ , ())})
is-ax? p₀′   _ = no (λ {(_ , ())})
is-ax? p₁    _ = no (λ {(_ , ())})
is-ax? p₁′   _ = no (λ {(_ , ())})
is-ax? p₂    _ = no (λ {(_ , ())})
is-ax? p₂′   _ = no (λ {(_ , ())})
