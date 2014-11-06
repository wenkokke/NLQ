------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Logic.Polarity


module Logic.Type.Polarised {ℓ} (Univ : Polarity → Set ℓ) where


open import Logic.Type (Σ Polarity Univ)


data Polarised : Polarity → Type → Set ℓ where
  el   : ∀ {p} (A : Univ p) → Polarised p (el (p , A))
  _⊗_  : ∀ {A B} (A⁺ : Polarised + A) (B⁺ : Polarised + B) → Polarised + (A ⊗ B)
  _⇚_  : ∀ {A B} (A⁺ : Polarised + A) (B⁻ : Polarised - B) → Polarised + (A ⇚ B)
  _⇛_  : ∀ {A B} (A⁻ : Polarised - A) (B⁺ : Polarised + B) → Polarised + (A ⇛ B)
  _⊕_  : ∀ {A B} (A⁻ : Polarised - A) (B⁻ : Polarised - B) → Polarised - (A ⊕ B)
  _⇐_  : ∀ {A B} (A⁻ : Polarised - A) (B⁺ : Polarised + B) → Polarised - (A ⇐ B)
  _⇒_  : ∀ {A B} (A⁺ : Polarised + A) (B⁻ : Polarised - B) → Polarised - (A ⇒ B)


private
  -- We can attempt to prove correctness in the following manner:
  --
  --  1. define a function `forget` which syntactically transforms a
  --     polarised context to a context (done with a macro to ensure
  --     that there are no typos.
  --
  --  2. proved a proof that `forget` returns the correct context, i.e.
  --     the context for which we've given a polarity proof.
  --
  -- What this gives us is the certainty that we didn't make any typos
  -- in the definition of `Polarised`, esp. in the matching of `Polarised`
  -- constructors to `Context` constructors... *snore*

  forget : ∀ {p A} (Aᴾ : Polarised p A) → Type
  forget (el A)  = el (_ , A)
  forget (A ⊗ B) = forget A ⊗ forget B
  forget (A ⇚ B) = forget A ⇚ forget B
  forget (A ⇛ B) = forget A ⇛ forget B
  forget (A ⊕ B) = forget A ⊕ forget B
  forget (A ⇐ B) = forget A ⇐ forget B
  forget (A ⇒ B) = forget A ⇒ forget B

  forget-correct : ∀ {p A} (Aᴾ : Polarised p A) → forget Aᴾ ≡ A
  forget-correct (el A)  = refl
  forget-correct (A ⊗ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇚ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇛ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⊕ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇐ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇒ B) rewrite forget-correct A | forget-correct B = refl
