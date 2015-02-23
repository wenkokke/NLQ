------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Logic.Polarity
open import Data.Product                               using (_×_; _,_)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Type.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type (Polarity × Univ)


data Polarised : Polarity → Type → Set ℓ where
  el   : ∀ {p}   (A  : Univ)                               → Polarised p (el (p , A))
  □_   : ∀ {A}   (A⁻ : Polarised - A)                      → Polarised - (□ A)
  ◇_   : ∀ {A}   (A⁺ : Polarised + A)                      → Polarised + (◇ A)
  _⊗_  : ∀ {A B} (A⁺ : Polarised + A) (B⁺ : Polarised + B) → Polarised + (A ⊗ B)
  _⇚_  : ∀ {A B} (A⁺ : Polarised + A) (B⁻ : Polarised - B) → Polarised + (A ⇚ B)
  _⇛_  : ∀ {A B} (A⁻ : Polarised - A) (B⁺ : Polarised + B) → Polarised + (A ⇛ B)
  _⊕_  : ∀ {A B} (A⁻ : Polarised - A) (B⁻ : Polarised - B) → Polarised - (A ⊕ B)
  _⇒_  : ∀ {A B} (A⁺ : Polarised + A) (B⁻ : Polarised - B) → Polarised - (A ⇒ B)
  _⇐_  : ∀ {A B} (A⁻ : Polarised - A) (B⁺ : Polarised + B) → Polarised - (A ⇐ B)


data Negative : Type → Set ℓ where
  el  : (A   : Univ) → Negative (el (- , A))
  □_  : (A   : Type) → Negative (□ A)
  _⊕_ : (A B : Type) → Negative (A ⊕ B)
  _⇒_ : (A B : Type) → Negative (A ⇒ B)
  _⇐_ : (A B : Type) → Negative (A ⇐ B)


Negative? : (A : Type) → Dec (Negative A)
Negative? (el (+ , A)) = no (λ ())
Negative? (el (- , A)) = yes (el A)
Negative?     (□   A)  = yes (□   A)
Negative?     (◇   A)  = no (λ ())
Negative?     (A ⇒ B)  = yes (A ⇒ B)
Negative?     (A ⇐ B)  = yes (A ⇐ B)
Negative?     (A ⇚ B)  = no (λ ())
Negative?     (A ⇛ B)  = no (λ ())
Negative?     (A ⊗ B)  = no (λ ())
Negative?     (A ⊕ B)  = yes (A ⊕ B)


data Positive : Type → Set ℓ where
  el  : (A   : Univ) → Positive (el (+ , A))
  ◇_  : (A   : Type) → Positive (◇ A)
  _⊗_ : (A B : Type) → Positive (A ⊗ B)
  _⇚_ : (A B : Type) → Positive (A ⇚ B)
  _⇛_ : (A B : Type) → Positive (A ⇛ B)


Positive? : (A : Type) → Dec (Positive A)
Positive? (el (+ , A)) = yes (el A)
Positive? (el (- , A)) = no (λ ())
Positive?     (□   A)  = no (λ ())
Positive?     (◇   A)  = yes (◇ A)
Positive?     (A ⇒ B)  = no (λ ())
Positive?     (A ⇐ B)  = no (λ ())
Positive?     (A ⇚ B)  = yes (A ⇚ B)
Positive?     (A ⇛ B)  = yes (A ⇛ B)
Positive?     (A ⊗ B)  = yes (A ⊗ B)
Positive?     (A ⊕ B)  = no (λ ())


Polarity? : (A : Type) → Positive A ⊎ Negative A
Polarity? (el (+ , A)) = inj₁ (el A)
Polarity? (el (- , A)) = inj₂ (el A)
Polarity?     (□   A)  = inj₂ (□ A)
Polarity?     (◇   A)  = inj₁ (◇ A)
Polarity?     (A ⇒ B)  = inj₂ (A ⇒ B)
Polarity?     (A ⇐ B)  = inj₂ (A ⇐ B)
Polarity?     (A ⇚ B)  = inj₁ (A ⇚ B)
Polarity?     (A ⇛ B)  = inj₁ (A ⇛ B)
Polarity?     (A ⊗ B)  = inj₁ (A ⊗ B)
Polarity?     (A ⊕ B)  = inj₂ (A ⊕ B)


module Correct where
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
  forget {p} (el  A) = el (p , A)
  forget     (□   A) = □ (forget A)
  forget     (◇   A) = ◇ (forget A)
  forget     (A ⊗ B) = forget A ⊗ forget B
  forget     (A ⇚ B) = forget A ⇚ forget B
  forget     (A ⇛ B) = forget A ⇛ forget B
  forget     (A ⊕ B) = forget A ⊕ forget B
  forget     (A ⇐ B) = forget A ⇐ forget B
  forget     (A ⇒ B) = forget A ⇒ forget B

  forget-correct : ∀ {p A} (Aᴾ : Polarised p A) → forget Aᴾ ≡ A
  forget-correct (el  A) = refl
  forget-correct (□   A) rewrite forget-correct A = refl
  forget-correct (◇   A) rewrite forget-correct A = refl
  forget-correct (A ⊗ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇚ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇛ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⊕ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇐ B) rewrite forget-correct A | forget-correct B = refl
  forget-correct (A ⇒ B) rewrite forget-correct A | forget-correct B = refl

  Positive-correct : ∀ {A} (A⁺ : Polarised + A) → Positive A
  Positive-correct (el  _) = el  _
  Positive-correct (◇   _) = ◇   _
  Positive-correct (_ ⊗ _) = _ ⊗ _
  Positive-correct (_ ⇚ _) = _ ⇚ _
  Positive-correct (_ ⇛ _) = _ ⇛ _

  Negative-correct : ∀ {A} (A⁻ : Polarised - A) → Negative A
  Negative-correct (el  _) = el  _
  Negative-correct (□   _) = □   _
  Negative-correct (_ ⊕ _) = _ ⊕ _
  Negative-correct (_ ⇒ _) = _ ⇒ _
  Negative-correct (_ ⇐ _) = _ ⇐ _
