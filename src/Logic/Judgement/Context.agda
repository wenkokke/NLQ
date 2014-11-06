------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Category
open import Algebra using (module Monoid; Monoid)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Judgement.Context {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ
open import Logic.Type.Context Univ as Context hiding (functor; module Simple)
open import Logic.Judgement Type Type

infix 5 _<⊢_ _⊢>_

data JudgementContext : Set ℓ where
  _<⊢_ : Context → Type → JudgementContext
  _⊢>_ : Type → Context → JudgementContext


-- Proofs which show that constructors of judgement contexts (as all
-- Agda data-constructors) respect equality.

<⊢-injective : ∀ {I J K L} → I <⊢ J ≡ K <⊢ L → I ≡ K × J ≡ L
<⊢-injective refl = refl , refl

⊢>-injective : ∀ {I J K L} → I ⊢> J ≡ K ⊢> L → I ≡ K × J ≡ L
⊢>-injective refl = refl , refl


-- TODO Think. This here is really senseless abstraction.


module Simple where

  open Context.Simple renaming (_[_] to _[_]′; _<_> to _<_>′)

  -- Apply a context to a type by plugging the type into the context.
  _[_] : JudgementContext → Type → Judgement
  (A <⊢ B) [ C ] = A [ C ]′ ⊢ B
  (A ⊢> B) [ C ] = A ⊢ B [ C ]′

  -- Insert a context into a judgement context
  _<_> : JudgementContext → Context → JudgementContext
  _<_> (A <⊢ B) C = A < C >′ <⊢ B
  _<_> (A ⊢> B) C = A ⊢> B < C >′


functor : Functor [ discrete JudgementContext × discrete Type ] (discrete Judgement)
functor = record
  { F₀           = λ {(J , A) → J [ A ]}
  ; F₁           = λ {(tt , tt) → tt}
  ; identity     = refl
  ; homomorphism = refl
  ; F-resp-≈     = λ _ → refl
  }
  where open Simple


-- Proofs regarding "structural contexts", i.e. contexts that can be
-- seen as representing structure, which would normally be shown with
-- commas.

infix 5 is-structuralᴸ_ is-structuralᴸ?_

data is-structuralᴸ_ : Context → Set ℓ where
  []   : is-structuralᴸ []
  _⊗>_ : (A : Type) {B : Context} (p : is-structuralᴸ B) → is-structuralᴸ A ⊗> B
  _<⊗_ : {A : Context} (p : is-structuralᴸ A) (B : Type) → is-structuralᴸ A <⊗ B

is-structuralᴸ?_ : (A : Context) → Dec (is-structuralᴸ A)
is-structuralᴸ? []       = yes []
is-structuralᴸ? A ⊗> B with is-structuralᴸ? B
is-structuralᴸ? A ⊗> _ | yes B = yes (A ⊗> B)
is-structuralᴸ? A ⊗> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-structuralᴸ A ⊗> B → is-structuralᴸ B
        lem (A ⊗> B) = B
is-structuralᴸ? A <⊗ B with is-structuralᴸ? A
is-structuralᴸ? _ <⊗ B | yes A = yes (A <⊗ B)
is-structuralᴸ? _ <⊗ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-structuralᴸ A <⊗ B → is-structuralᴸ A
        lem (A <⊗ B) = A
is-structuralᴸ? A ⇛> B = no (λ ())
is-structuralᴸ? A ⇚> B = no (λ ())
is-structuralᴸ? A ⊕> B = no (λ ())
is-structuralᴸ? A ⇒> B = no (λ ())
is-structuralᴸ? A ⇐> B = no (λ ())
is-structuralᴸ? A <⇛ B = no (λ ())
is-structuralᴸ? A <⇚ B = no (λ ())
is-structuralᴸ? A <⊕ B = no (λ ())
is-structuralᴸ? A <⇒ B = no (λ ())
is-structuralᴸ? A <⇐ B = no (λ ())


infix 2 is-structural_ is-structural?_

data is-structural_ : JudgementContext → Set ℓ where
  _<⊢_ : {A : Context} (p : is-structuralᴸ A) (B : Type) → is-structural (A <⊢ B)

is-structural?_ : (J : JudgementContext) → Dec (is-structural J)
is-structural? A <⊢ B with (is-structuralᴸ? A)
is-structural? _ <⊢ B | yes A = yes (A <⊢ B)
is-structural? _ <⊢ B | no ¬A = no (¬A ∘ lem)
  where
    lem : ∀ {A B} → is-structural A <⊢ B → is-structuralᴸ A
    lem (A <⊢ B) = A
is-structural? A ⊢> B = no (λ ())


-- Proofs regarding "input contexts", i.e. contexts whose type can be
-- seen as "consuming something".

infix 5 is-inputᴿ_ is-inputᴿ?_

data is-inputᴿ_ : Context → Set ℓ where
  _⇐>_ : (A : Type) {B : Context} (p : is-structuralᴸ B) → is-inputᴿ A ⇐> B
  _<⇒_ : {A : Context} (p : is-structuralᴸ A) (B : Type) → is-inputᴿ A <⇒ B
  _⇒>_ : (A : Type) {B : Context} (p : is-inputᴿ B) → is-inputᴿ A ⇒> B
  _<⇐_ : {A : Context} (p : is-inputᴿ A) (B : Type) → is-inputᴿ A <⇐ B

is-inputᴿ?_ : (A : Context) → Dec (is-inputᴿ A)
is-inputᴿ? []     = no (λ ())
is-inputᴿ? A ⊗> B = no (λ ())
is-inputᴿ? A ⇛> B = no (λ ())
is-inputᴿ? A ⇚> B = no (λ ())
is-inputᴿ? A ⊕> B = no (λ ())
is-inputᴿ? A ⇒> B with (is-inputᴿ? B)
is-inputᴿ? A ⇒> _ | yes B = yes (A ⇒> B)
is-inputᴿ? A ⇒> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-inputᴿ A ⇒> B → is-inputᴿ B
        lem (A ⇒> B) = B
is-inputᴿ? A ⇐> B with (is-structuralᴸ? B)
is-inputᴿ? A ⇐> _ | yes B = yes (A ⇐> B)
is-inputᴿ? A ⇐> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-inputᴿ A ⇐> B → is-structuralᴸ B
        lem (A ⇐> B) = B
is-inputᴿ? A <⊗ B = no (λ ())
is-inputᴿ? A <⇛ B = no (λ ())
is-inputᴿ? A <⇚ B = no (λ ())
is-inputᴿ? A <⊕ B = no (λ ())
is-inputᴿ? A <⇒ B with (is-structuralᴸ? A)
is-inputᴿ? _ <⇒ B | yes A = yes (A <⇒ B)
is-inputᴿ? _ <⇒ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-inputᴿ A <⇒ B → is-structuralᴸ A
        lem (A <⇒ B) = A
is-inputᴿ? A <⇐ B with (is-inputᴿ? A)
is-inputᴿ? _ <⇐ B | yes A = yes (A <⇐ B)
is-inputᴿ? _ <⇐ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-inputᴿ A <⇐ B → is-inputᴿ A
        lem (A <⇐ B) = A


infix 2 is-input_ is-input?_

data is-input_ : JudgementContext → Set ℓ where
  _<⊢_ : {A : Context} (p : is-structuralᴸ A) (B : Type) → is-input A <⊢ B
  _⊢>_ : (A : Type) {B : Context} (p : is-inputᴿ B) → is-input A ⊢> B

is-input?_ : (J : JudgementContext) → Dec (is-input J)
is-input? A <⊢ B with (is-structuralᴸ? A)
is-input? _ <⊢ B | yes A = yes (A <⊢ B)
is-input? _ <⊢ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-input A <⊢ B → is-structuralᴸ A
        lem (A <⊢ B) = A
is-input? A ⊢> B with (is-inputᴿ? B)
is-input? A ⊢> _ | yes B = yes (A ⊢> B)
is-input? A ⊢> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-input A ⊢> B → is-inputᴿ B
        lem (A ⊢> B) = B


-- Proofs regarding "output contexts", i.e. contexts whose type can be
-- seen as "producing something".

infix 5 is-outputᴿ_ is-outputᴿ?_

data is-outputᴿ_ : Context → Set ℓ where
  []   : is-outputᴿ []
  _⇒>_ : (A : Type) {B : Context} (p : is-outputᴿ B) → is-outputᴿ A ⇒> B
  _<⇐_ : {A : Context} (p : is-outputᴿ A) (B : Type) → is-outputᴿ A <⇐ B


is-outputᴿ?_ : (A : Context) → Dec (is-outputᴿ A)
is-outputᴿ? [] = yes []
is-outputᴿ? A ⊗> B = no (λ ())
is-outputᴿ? A ⇛> B = no (λ ())
is-outputᴿ? A ⇚> B = no (λ ())
is-outputᴿ? A ⊕> B = no (λ ())
is-outputᴿ? A ⇒> B with (is-outputᴿ? B)
is-outputᴿ? A ⇒> _ | yes B = yes (A ⇒> B)
is-outputᴿ? A ⇒> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-outputᴿ A ⇒> B → is-outputᴿ B
        lem (A ⇒> B) = B
is-outputᴿ? A ⇐> B = no (λ ())
is-outputᴿ? A <⊗ B = no (λ ())
is-outputᴿ? A <⇛ B = no (λ ())
is-outputᴿ? A <⇚ B = no (λ ())
is-outputᴿ? A <⊕ B = no (λ ())
is-outputᴿ? A <⇒ B = no (λ ())
is-outputᴿ? A <⇐ B with (is-outputᴿ? A)
is-outputᴿ? _ <⇐ B | yes A = yes (A <⇐ B)
is-outputᴿ? _ <⇐ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-outputᴿ A <⇐ B → is-outputᴿ A
        lem (A <⇐ B) = A


infix 2 is-output_ is-output?_

data is-output_ : JudgementContext → Set ℓ where
  _⊢>_ : (A : Type) {B : Context} (p : is-outputᴿ B) → is-output A ⊢> B


is-output?_ : (J : JudgementContext) → Dec (is-output J)
is-output? A <⊢ B = no (λ ())
is-output? A ⊢> B with (is-outputᴿ? B)
is-output? A ⊢> _ | yes B = yes (A ⊢> B)
is-output? A ⊢> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-output A ⊢> B → is-outputᴿ B
        lem (A ⊢> B) = B
