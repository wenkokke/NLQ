------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.Classical.Ordered.LambekGrishin.ResMon.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type             Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ


infix 1 LG_

data LG_ : Judgement → Set ℓ where

  ax     : ∀ {A}       → LG el A ⊢ el A

  -- rules for residuation and monotonicity
  mon-⊗  : ∀ {A B C D} → LG A ⊢ B → LG C ⊢ D → LG A ⊗ C ⊢ B ⊗ D
  mon-⇒  : ∀ {A B C D} → LG A ⊢ B → LG C ⊢ D → LG B ⇒ C ⊢ A ⇒ D
  mon-⇐  : ∀ {A B C D} → LG A ⊢ B → LG C ⊢ D → LG A ⇐ D ⊢ B ⇐ C
  res-⇒⊗ : ∀ {A B C}   → LG B ⊢ A ⇒ C → LG A ⊗ B ⊢ C
  res-⊗⇒ : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG B ⊢ A ⇒ C
  res-⇐⊗ : ∀ {A B C}   → LG A ⊢ C ⇐ B → LG A ⊗ B ⊢ C
  res-⊗⇐ : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG A ⊢ C ⇐ B

  -- rules for co-residuation and co-monotonicity
  mon-⊕  : ∀ {A B C D} → LG A ⊢ B → LG C ⊢ D → LG A ⊕ C ⊢ B ⊕ D
  mon-⇛  : ∀ {A B C D} → LG C ⊢ D → LG A ⊢ B → LG D ⇛ A ⊢ C ⇛ B
  mon-⇚  : ∀ {A B C D} → LG A ⊢ B → LG C ⊢ D → LG A ⇚ D ⊢ B ⇚ C
  res-⇛⊕ : ∀ {A B C}   → LG B ⇛ C ⊢ A → LG C ⊢ B ⊕ A
  res-⊕⇛ : ∀ {A B C}   → LG C ⊢ B ⊕ A → LG B ⇛ C ⊢ A
  res-⊕⇚ : ∀ {A B C}   → LG C ⊢ B ⊕ A → LG C ⇚ A ⊢ B
  res-⇚⊕ : ∀ {A B C}   → LG C ⇚ A ⊢ B → LG C ⊢ B ⊕ A

  -- grishin distributives
  grish₁ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG C ⇛ A ⊢ D ⇐ B
  grish₂ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG C ⇛ B ⊢ A ⇒ D
  grish₃ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG B ⇚ D ⊢ A ⇒ C
  grish₄ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG A ⇚ D ⊢ C ⇐ B


-- Proofs which show that constructors of terms (as all Agda
-- data-constructors) respect equality.

mon-⊗-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → mon-⊗ {A} {B} {C} {D} f₁ f₂ ≡ mon-⊗ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
mon-⊗-injective refl = refl , refl
mon-⇒-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → mon-⇒ {A} {B} {C} {D} f₁ f₂ ≡ mon-⇒ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
mon-⇒-injective refl = refl , refl
mon-⇐-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → mon-⇐ {A} {B} {C} {D} f₁ f₂ ≡ mon-⇐ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
mon-⇐-injective refl = refl , refl

res-⇒⊗-injective : ∀ {A B C f g} → res-⇒⊗ {A} {B} {C} f ≡ res-⇒⊗ g → f ≡ g
res-⇒⊗-injective refl = refl
res-⊗⇒-injective : ∀ {A B C f g} → res-⊗⇒ {A} {B} {C} f ≡ res-⊗⇒ g → f ≡ g
res-⊗⇒-injective refl = refl
res-⇐⊗-injective : ∀ {A B C f g} → res-⇐⊗ {A} {B} {C} f ≡ res-⇐⊗ g → f ≡ g
res-⇐⊗-injective refl = refl
res-⊗⇐-injective : ∀ {A B C f g} → res-⊗⇐ {A} {B} {C} f ≡ res-⊗⇐ g → f ≡ g
res-⊗⇐-injective refl = refl

mon-⊕-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → mon-⊕ {A} {B} {C} {D} f₁ f₂ ≡ mon-⊕ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
mon-⊕-injective refl = refl , refl
mon-⇛-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → mon-⇛ {A} {B} {C} {D} f₁ f₂ ≡ mon-⇛ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
mon-⇛-injective refl = refl , refl
mon-⇚-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → mon-⇚ {A} {B} {C} {D} f₁ f₂ ≡ mon-⇚ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
mon-⇚-injective refl = refl , refl

res-⇛⊕-injective : ∀ {A B C f g} → res-⇛⊕ {A} {B} {C} f ≡ res-⇛⊕ g → f ≡ g
res-⇛⊕-injective refl = refl
res-⊕⇛-injective : ∀ {A B C f g} → res-⊕⇛ {A} {B} {C} f ≡ res-⊕⇛ g → f ≡ g
res-⊕⇛-injective refl = refl
res-⊕⇚-injective : ∀ {A B C f g} → res-⊕⇚ {A} {B} {C} f ≡ res-⊕⇚ g → f ≡ g
res-⊕⇚-injective refl = refl
res-⇚⊕-injective : ∀ {A B C f g} → res-⇚⊕ {A} {B} {C} f ≡ res-⇚⊕ g → f ≡ g
res-⇚⊕-injective refl = refl

grish₁-injective : ∀ {A B C D f g} → grish₁ {A} {B} {C} {D} f ≡ grish₁ g → f ≡ g
grish₁-injective refl = refl
grish₂-injective : ∀ {A B C D f g} → grish₂ {A} {B} {C} {D} f ≡ grish₂ g → f ≡ g
grish₂-injective refl = refl
grish₃-injective : ∀ {A B C D f g} → grish₃ {A} {B} {C} {D} f ≡ grish₃ g → f ≡ g
grish₃-injective refl = refl
grish₄-injective : ∀ {A B C D f g} → grish₄ {A} {B} {C} {D} f ≡ grish₄ g → f ≡ g
grish₄-injective refl = refl


-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `LG`.
ax′ : ∀ {A} → LG A ⊢ A
ax′ {el A}  = ax
ax′ {A ⊗ B} = mon-⊗ ax′ ax′
ax′ {A ⇚ B} = mon-⇚ ax′ ax′
ax′ {A ⇛ B} = mon-⇛ ax′ ax′
ax′ {A ⊕ B} = mon-⊕ ax′ ax′
ax′ {A ⇐ B} = mon-⇐ ax′ ax′
ax′ {A ⇒ B} = mon-⇒ ax′ ax′

-- Derived rules for two-step residuations.
res-⇐⇒′ : ∀ {A B C} → LG A ⊢ C ⇐ B → LG B ⊢ A ⇒ C
res-⇐⇒′ = res-⊗⇒ ∘ res-⇐⊗
res-⇒⇐′ : ∀ {A B C} → LG B ⊢ A ⇒ C → LG A ⊢ C ⇐ B
res-⇒⇐′ = res-⊗⇐ ∘ res-⇒⊗

-- Derived rules for two-step co-residuations.
res-⇚⇒′ : ∀ {A B C} → LG C ⇚ A ⊢ B → LG B ⇛ C ⊢ A
res-⇚⇒′ = res-⊕⇛ ∘ res-⇚⊕
res-⇒⇚′ : ∀ {A B C} → LG B ⇛ C ⊢ A → LG C ⇚ A ⊢ B
res-⇒⇚′ = res-⊕⇚ ∘ res-⇛⊕

-- Derived rules for application.
appl-⇒′ : ∀ {A B C} → LG B ⊢ C → LG A ⊗ (A ⇒ B) ⊢ C
appl-⇒′ f = res-⇒⊗ (mon-⇒ ax′ f)
appl-⇐′ : ∀ {A B C} → LG B ⊢ C → LG (B ⇐ A) ⊗ A ⊢ C
appl-⇐′ f = res-⇐⊗ (mon-⇐ f ax′)

-- Derived rules for co-application.
appl-⇛′ : ∀ {A B C} → LG B ⊢ C → LG B ⊢ A ⊕ (A ⇛ C)
appl-⇛′ f = res-⇛⊕ (mon-⇛ ax′ f)
appl-⇚′ : ∀ {A B C} → LG B ⊢ C → LG B ⊢ (C ⇚ A) ⊕ A
appl-⇚′ f = res-⇚⊕ (mon-⇚ f ax′)


infix 5 is-ax_ is-ax?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-ax_ : ∀ {A B} (f : LG A ⊢ B) → Set ℓ
is-ax_ f = ∃ (λ A → f ≅ ax {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-ax?_ : ∀ {A B} (f : LG A ⊢ B) → Dec (is-ax f)
is-ax? ax         = yes (_ , H.refl)
is-ax? mon-⊗  _ _ = no (λ {(_ , ())})
is-ax? mon-⇒  _ _ = no (λ {(_ , ())})
is-ax? mon-⇐  _ _ = no (λ {(_ , ())})
is-ax? res-⇒⊗ _   = no (λ {(_ , ())})
is-ax? res-⊗⇒ _   = no (λ {(_ , ())})
is-ax? res-⇐⊗ _   = no (λ {(_ , ())})
is-ax? res-⊗⇐ _   = no (λ {(_ , ())})
is-ax? res-⇛⊕ _   = no (λ {(_ , ())})
is-ax? res-⊕⇛ _   = no (λ {(_ , ())})
is-ax? res-⊕⇚ _   = no (λ {(_ , ())})
is-ax? res-⇚⊕ _   = no (λ {(_ , ())})
is-ax? mon-⊕  _ _ = no (λ {(_ , ())})
is-ax? mon-⇛  _ _ = no (λ {(_ , ())})
is-ax? mon-⇚  _ _ = no (λ {(_ , ())})
is-ax? grish₁ _   = no (λ {(_ , ())})
is-ax? grish₂ _   = no (λ {(_ , ())})
is-ax? grish₃ _   = no (λ {(_ , ())})
is-ax? grish₄ _   = no (λ {(_ , ())})


f:elA⊢elA→f≡ax : ∀ {A} (f : LG el A ⊢ el A) → f ≡ ax
f:elA⊢elA→f≡ax ax = refl
