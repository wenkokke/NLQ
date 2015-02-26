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

  ax  : ∀ {A}       → LG el A ⊢ el A

  -- rules for residuation and monotonicity for (□ , ◇)
  m□  : ∀ {A B}     → LG   A ⊢   B → LG □ A ⊢ □ B
  m◇  : ∀ {A B}     → LG   A ⊢   B → LG ◇ A ⊢ ◇ B
  r□◇ : ∀ {A B}     → LG   A ⊢ □ B → LG ◇ A ⊢   B
  r◇□ : ∀ {A B}     → LG ◇ A ⊢   B → LG   A ⊢ □ B

  -- rules for residuation and monotonicity for (₀ , ⁰)
  m⁰  : ∀ {A B}     → LG B ⊢   A   → LG   A ⁰ ⊢   B ⁰
  m₀  : ∀ {A B}     → LG B ⊢   A   → LG ₀ A   ⊢ ₀ B
  r⁰₀ : ∀ {A B}     → LG B ⊢   A ⁰ → LG   A   ⊢ ₀ B
  r₀⁰ : ∀ {A B}     → LG B ⊢ ₀ A   → LG   A   ⊢   B ⁰

  -- rules for residuation and monotonicity for (₁ , ¹)
  m₁  : ∀ {A B}     → LG   B   ⊢ A   → LG ₁ A   ⊢ ₁ B
  m¹  : ∀ {A B}     → LG   B   ⊢ A   → LG   A ¹ ⊢   B ¹
  r¹₁ : ∀ {A B}     → LG   B ¹ ⊢ A   → LG ₁ A   ⊢   B
  r₁¹ : ∀ {A B}     → LG ₁ B   ⊢ A   → LG   A ¹ ⊢   B

  -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
  m⊗  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⊗ C ⊢ B ⊗ D
  m⇒  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG B ⇒ C ⊢ A ⇒ D
  m⇐  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⇐ D ⊢ B ⇐ C
  r⇒⊗ : ∀ {A B C}   → LG B ⊢ A ⇒ C → LG A ⊗ B ⊢ C
  r⊗⇒ : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG B ⊢ A ⇒ C
  r⇐⊗ : ∀ {A B C}   → LG A ⊢ C ⇐ B → LG A ⊗ B ⊢ C
  r⊗⇐ : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG A ⊢ C ⇐ B

  -- rules for residuation and monotonicity for (⇚ , ⊕ , ⇛)
  m⊕  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⊕ C ⊢ B ⊕ D
  m⇛  : ∀ {A B C D} → LG C ⊢ D     → LG A ⊢ B     → LG D ⇛ A ⊢ C ⇛ B
  m⇚  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⇚ D ⊢ B ⇚ C
  r⇛⊕ : ∀ {A B C}   → LG B ⇛ C ⊢ A → LG C ⊢ B ⊕ A
  r⊕⇛ : ∀ {A B C}   → LG C ⊢ B ⊕ A → LG B ⇛ C ⊢ A
  r⊕⇚ : ∀ {A B C}   → LG C ⊢ B ⊕ A → LG C ⇚ A ⊢ B
  r⇚⊕ : ∀ {A B C}   → LG C ⇚ A ⊢ B → LG C ⊢ B ⊕ A

  -- grishin distributives
  d⇛⇐ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG C ⇛ A ⊢ D ⇐ B
  d⇛⇒ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG C ⇛ B ⊢ A ⇒ D
  d⇚⇒ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG B ⇚ D ⊢ A ⇒ C
  d⇚⇐ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG A ⇚ D ⊢ C ⇐ B


-- Proofs which show that constructors of terms (as all Agda
-- data-constructors) respect equality.

m⊗-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → m⊗ {A} {B} {C} {D} f₁ f₂ ≡ m⊗ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
m⊗-injective refl = refl , refl
m⇒-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → m⇒ {A} {B} {C} {D} f₁ f₂ ≡ m⇒ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
m⇒-injective refl = refl , refl
m⇐-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → m⇐ {A} {B} {C} {D} f₁ f₂ ≡ m⇐ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
m⇐-injective refl = refl , refl

r⇒⊗-injective : ∀ {A B C f g} → r⇒⊗ {A} {B} {C} f ≡ r⇒⊗ g → f ≡ g
r⇒⊗-injective refl = refl
r⊗⇒-injective : ∀ {A B C f g} → r⊗⇒ {A} {B} {C} f ≡ r⊗⇒ g → f ≡ g
r⊗⇒-injective refl = refl
r⇐⊗-injective : ∀ {A B C f g} → r⇐⊗ {A} {B} {C} f ≡ r⇐⊗ g → f ≡ g
r⇐⊗-injective refl = refl
r⊗⇐-injective : ∀ {A B C f g} → r⊗⇐ {A} {B} {C} f ≡ r⊗⇐ g → f ≡ g
r⊗⇐-injective refl = refl

m⊕-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → m⊕ {A} {B} {C} {D} f₁ f₂ ≡ m⊕ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
m⊕-injective refl = refl , refl
m⇛-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → m⇛ {A} {B} {C} {D} f₁ f₂ ≡ m⇛ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
m⇛-injective refl = refl , refl
m⇚-injective : ∀ {A B C D f₁ f₂ g₁ g₂} → m⇚ {A} {B} {C} {D} f₁ f₂ ≡ m⇚ g₁ g₂ → f₁ ≡ g₁ × f₂ ≡ g₂
m⇚-injective refl = refl , refl

r⇛⊕-injective : ∀ {A B C f g} → r⇛⊕ {A} {B} {C} f ≡ r⇛⊕ g → f ≡ g
r⇛⊕-injective refl = refl
r⊕⇛-injective : ∀ {A B C f g} → r⊕⇛ {A} {B} {C} f ≡ r⊕⇛ g → f ≡ g
r⊕⇛-injective refl = refl
r⊕⇚-injective : ∀ {A B C f g} → r⊕⇚ {A} {B} {C} f ≡ r⊕⇚ g → f ≡ g
r⊕⇚-injective refl = refl
r⇚⊕-injective : ∀ {A B C f g} → r⇚⊕ {A} {B} {C} f ≡ r⇚⊕ g → f ≡ g
r⇚⊕-injective refl = refl

d⇛⇐-injective : ∀ {A B C D f g} → d⇛⇐ {A} {B} {C} {D} f ≡ d⇛⇐ g → f ≡ g
d⇛⇐-injective refl = refl
d⇛⇒-injective : ∀ {A B C D f g} → d⇛⇒ {A} {B} {C} {D} f ≡ d⇛⇒ g → f ≡ g
d⇛⇒-injective refl = refl
d⇚⇒-injective : ∀ {A B C D f g} → d⇚⇒ {A} {B} {C} {D} f ≡ d⇚⇒ g → f ≡ g
d⇚⇒-injective refl = refl
d⇚⇐-injective : ∀ {A B C D f g} → d⇚⇐ {A} {B} {C} {D} f ≡ d⇚⇐ g → f ≡ g
d⇚⇐-injective refl = refl


-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `LG`.
ax′ : ∀ {A} → LG A ⊢ A
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
r⇐⇒′ : ∀ {A B C} → LG A ⊢ C ⇐ B → LG B ⊢ A ⇒ C
r⇐⇒′ = r⊗⇒ ∘ r⇐⊗
r⇒⇐′ : ∀ {A B C} → LG B ⊢ A ⇒ C → LG A ⊢ C ⇐ B
r⇒⇐′ = r⊗⇐ ∘ r⇒⊗

-- Derived rules for two-step co-residuations.
r⇚⇛′ : ∀ {A B C} → LG C ⇚ A ⊢ B → LG B ⇛ C ⊢ A
r⇚⇛′ = r⊕⇛ ∘ r⇚⊕
r⇛⇚′ : ∀ {A B C} → LG B ⇛ C ⊢ A → LG C ⇚ A ⊢ B
r⇛⇚′ = r⊕⇚ ∘ r⇛⊕

-- Derived rules for application.
appl-⇒′ : ∀ {A B C} → LG B ⊢ C → LG A ⊗ (A ⇒ B) ⊢ C
appl-⇒′ f = r⇒⊗ (m⇒ ax′ f)
appl-⇐′ : ∀ {A B C} → LG B ⊢ C → LG (B ⇐ A) ⊗ A ⊢ C
appl-⇐′ f = r⇐⊗ (m⇐ f ax′)

-- Derived rules for co-application.
appl-⇛′ : ∀ {A B C} → LG B ⊢ C → LG B ⊢ A ⊕ (A ⇛ C)
appl-⇛′ f = r⇛⊕ (m⇛ ax′ f)
appl-⇚′ : ∀ {A B C} → LG B ⊢ C → LG B ⊢ (C ⇚ A) ⊕ A
appl-⇚′ f = r⇚⊕ (m⇚ f ax′)


infix 5 is-ax_ is-ax?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-ax_ : ∀ {A B} (f : LG A ⊢ B) → Set ℓ
is-ax_ f = ∃ (λ A → f ≅ ax {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-ax?_ : ∀ {A B} (f : LG A ⊢ B) → Dec (is-ax f)
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


f:elA⊢elA→f≡ax : ∀ {A} (f : LG el A ⊢ el A) → f ≡ ax
f:elA⊢elA→f≡ax ax = refl
