------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra                                    using (Monoid)
open import Function                                   using (flip; _∘_)
open import Data.Product                               using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Unrestricted.Lambda.Type.Context.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Intuitionistic.Unrestricted.Lambda.Type         Univ as T
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.Context Univ as TC hiding (module Simple)


-- The below definition for polarised context enforces the top polarity
-- and the polarity of the hole. In doing so, it enforces that the contexts
-- maintain polarity---for instance, it excludes the context `A ⇒> ([] <⊗)`.
-- However, it makes no attempt to maintain polarity in the nested types (as
-- could be done with `Logic.Type.Polarised`).

data Polarised (p : Polarity) : Polarity → Context → Set ℓ where

  []   : Polarised p p []

  ₀>_  : {A : Context} (A⁻ : Polarised p - A) → Polarised p - (₀> A)
  _<⁰  : {A : Context} (A⁻ : Polarised p - A) → Polarised p - (A <⁰)
  ₁>_  : {A : Context} (A⁺ : Polarised p + A) → Polarised p + (₁> A)
  _<¹  : {A : Context} (A⁺ : Polarised p + A) → Polarised p + (A <¹)

  _⊗>_ : (A : Type) {B : Context} (B⁺ : Polarised p + B) → Polarised p + (A ⊗> B)
  _<⊗_ : {A : Context} (A⁺ : Polarised p + A) (B : Type) → Polarised p + (A <⊗ B)
  _⇒>_ : (A : Type) {B : Context} (B⁻ : Polarised p - B) → Polarised p - (A ⇒> B)
  _<⇒_ : {A : Context} (A⁺ : Polarised p + A) (B : Type) → Polarised p - (A <⇒ B)
-- Structural contexts refer to contexts consisting solely of products
-- or solely of sums.

Structural⁺ : Context → Set ℓ
Structural⁺ = Polarised + +

Structural⁻ : Context → Set ℓ
Structural⁻ = Polarised - -


module Simple where

  open TC.Simple renaming (_[_] to _[_]′; _<_> to _<_>′)

  -- Apply a context to a type by plugging the type into the context.
  _[_] : ∀ {p₁ p₂ A} → Polarised p₁ p₂ A → Type → Type
  []       [ A ] = A
  (₀> B)   [ A ] = ₀ (B [ A ])
  (₁> B)   [ A ] = ₁ (B [ A ])
  (B <⁰)   [ A ] = (B [ A ]) ⁰
  (B <¹)   [ A ] = (B [ A ]) ¹
  (B ⊗> C) [ A ] = B ⊗ (C [ A ])
  (B ⇒> C) [ A ] = B ⇒ (C [ A ])
  (C <⊗ B) [ A ] = (C [ A ]) ⊗ B
  (C <⇒ B) [ A ] = (C [ A ]) ⇒ B
  -- Compose two contexts to format new context.
  _<_> : ∀ {p₁ p₂ p₃ A B}
       → Polarised p₂ p₃ A → Polarised p₁ p₂ B → Polarised p₁ p₃ (A < B >′)
  []       < A > = A
  (₀> B)   < A > = ₀> (B < A >)
  (₁> B)   < A > = ₁> (B < A >)
  (B <⁰)   < A > = (B < A >) <⁰
  (B <¹)   < A > = (B < A >) <¹
  (B ⊗> C) < A > = B ⊗> (C < A >)
  (B ⇒> C) < A > = B ⇒> (C < A >)
  (C <⊗ B) < A > = (C < A >) <⊗ B
  (C <⇒ B) < A > = (C < A >) <⇒ B
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

  forget : ∀ {p₁ p₂ A} → Polarised p₁ p₂ A → Context
  forget []       = []
  forget (₀> A)   = ₀> forget A
  forget (₁> A)   = ₁> forget A
  forget (A <⁰)   = forget A <⁰
  forget (A <¹)   = forget A <¹
  forget (A ⊗> B) = A ⊗> forget B
  forget (A <⊗ B) = forget A <⊗ B
  forget (A ⇒> B) = A ⇒> forget B
  forget (A <⇒ B) = forget A <⇒ B
  forget-correct : ∀ {p₁ p₂ A} (Aᴾ : Polarised p₁ p₂ A) → forget Aᴾ ≡ A
  forget-correct []       = refl
  forget-correct (₀> A)   rewrite forget-correct A = refl
  forget-correct (₁> A)   rewrite forget-correct A = refl
  forget-correct (A <⁰)   rewrite forget-correct A = refl
  forget-correct (A <¹)   rewrite forget-correct A = refl
  forget-correct (A ⊗> B) rewrite forget-correct B = refl
  forget-correct (A <⊗ B) rewrite forget-correct A = refl
  forget-correct (A ⇒> B) rewrite forget-correct B = refl
  forget-correct (A <⇒ B) rewrite forget-correct A = refl
