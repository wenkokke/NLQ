------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.Lambek.ResMon.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ
open import Logic.Lambek.Type Univ
open import Logic.Judgement Type Type


infix 3 NL_

data NL_ : Judgement → Set ℓ where
  id     : ∀ {A}       → NL el A ⊢ el A

  -- rules for residuation and monotonicity
  res-⇒⊗ : ∀ {A B C}   → NL B ⊢ A ⇒ C → NL A ⊗ B ⊢ C
  res-⊗⇒ : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
  res-⇐⊗ : ∀ {A B C}   → NL A ⊢ C ⇐ B → NL A ⊗ B ⊢ C
  res-⊗⇐ : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B
  mon-⊗  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⊗ C ⊢ B ⊗ D
  mon-⇒  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇒ C ⊢ A ⇒ D
  mon-⇐  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇐ D ⊢ B ⇐ C


-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `NL`.
id′ : ∀ {A} {{p : True (is-valid? A)}} → NL A ⊢ A
id′ {{p}} with (toWitness p)
id′ | el A  = id
id′ | A ⊗ B = mon-⊗ (id′ {{p = fromWitness A}}) (id′ {{p = fromWitness B}})
id′ | A ⇐ B = mon-⇐ (id′ {{p = fromWitness A}}) (id′ {{p = fromWitness B}})
id′ | A ⇒ B = mon-⇒ (id′ {{p = fromWitness A}}) (id′ {{p = fromWitness B}})


-- Derived rules for two-step residuations.
res-⇐⇒′ : ∀ {A B C} → NL A ⊢ C ⇐ B → NL B ⊢ A ⇒ C
res-⇐⇒′ = res-⊗⇒ ∘ res-⇐⊗
res-⇒⇐′ : ∀ {A B C} → NL B ⊢ A ⇒ C → NL A ⊢ C ⇐ B
res-⇒⇐′ = res-⊗⇐ ∘ res-⇒⊗


-- Derived rules for application.
appl-⇒′ : ∀ {A B} {{p : True (is-valid? A ⇒ B)}} → NL A ⊗ (A ⇒ B) ⊢ B
appl-⇒′ = res-⇒⊗ id′
appl-⇐′ : ∀ {A B} {{p : True (is-valid? B ⇐ A)}} → NL (B ⇐ A) ⊗ A ⊢ B
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
