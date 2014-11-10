------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.Lambek.ResMon.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type Univ
open import Logic.Lambek.Judgement Univ


infix 3 NL_

data NL_ : Judgement → Set ℓ where

  id     : ∀ {A}       → NL el A ⊢ el A

  -- rules for residuation and monotonicity
  mon-⊗  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⊗ C ⊢ B ⊗ D
  mon-⇒  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇒ C ⊢ A ⇒ D
  mon-⇐  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇐ D ⊢ B ⇐ C
  res-⇒⊗ : ∀ {A B C}   → NL B ⊢ A ⇒ C → NL A ⊗ B ⊢ C
  res-⊗⇒ : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
  res-⇐⊗ : ∀ {A B C}   → NL A ⊢ C ⇐ B → NL A ⊗ B ⊢ C
  res-⊗⇐ : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B

  -- rules for co-residuation and co-monotonicity
  -- grishin distributives
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


-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `NL`.
id′ : ∀ {A} → NL A ⊢ A
id′ {el A}  = id
id′ {A ⊗ B} = mon-⊗ id′ id′
id′ {A ⇐ B} = mon-⇐ id′ id′
id′ {A ⇒ B} = mon-⇒ id′ id′

-- Derived rules for two-step residuations.
res-⇐⇒′ : ∀ {A B C} → NL A ⊢ C ⇐ B → NL B ⊢ A ⇒ C
res-⇐⇒′ = res-⊗⇒ ∘ res-⇐⊗
res-⇒⇐′ : ∀ {A B C} → NL B ⊢ A ⇒ C → NL A ⊢ C ⇐ B
res-⇒⇐′ = res-⊗⇐ ∘ res-⇒⊗

-- Derived rules for application.
appl-⇒′ : ∀ {A B} → NL A ⊗ (A ⇒ B) ⊢ B
appl-⇒′ = res-⇒⊗ id′
appl-⇐′ : ∀ {A B} → NL (B ⇐ A) ⊗ A ⊢ B
appl-⇐′ = res-⇐⊗ id′


infix 5 is-id_ is-id?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-id_ : ∀ {A B} (f : NL A ⊢ B) → Set ℓ
is-id_ f = ∃ (λ A → f ≅ id {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-id?_ : ∀ {A B} (f : NL A ⊢ B) → Dec (is-id f)
is-id? id         = yes (_ , H.refl)
is-id? mon-⊗  _ _ = no (λ {(_ , ())})
is-id? mon-⇒  _ _ = no (λ {(_ , ())})
is-id? mon-⇐  _ _ = no (λ {(_ , ())})
is-id? res-⇒⊗ _   = no (λ {(_ , ())})
is-id? res-⊗⇒ _   = no (λ {(_ , ())})
is-id? res-⇐⊗ _   = no (λ {(_ , ())})
is-id? res-⊗⇐ _   = no (λ {(_ , ())})
f:elA⊢elA→f≡id : ∀ {A} (f : NL el A ⊢ el A) → f ≡ id
f:elA⊢elA→f≡id id = refl
