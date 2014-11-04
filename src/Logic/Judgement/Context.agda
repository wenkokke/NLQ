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
open import Logic.Type.Context Univ as Context hiding (functor)
open import Logic.Judgement Type Type
open Functor Context.functor renaming (F₁ to _[_]′)


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


-- Apply a context to a type by plugging the type into the context.
_[_] : JudgementContext → Type → Judgement
(A <⊢ B) [ C ] = A [ C ]′ ⊢ B
(A ⊢> B) [ C ] = A ⊢ B [ C ]′


-- Proofs regarding "structural contexts", i.e. contexts that can be
-- seen as representing structure, which would normally be shown with
-- commas.

infix 5 is-structural-lhs_ is-structural-lhs?_

data is-structural-lhs_ : Context → Set ℓ where
  []   : is-structural-lhs []
  _⊗>_ : (A : Type) {B : Context} (p : is-structural-lhs B) → is-structural-lhs A ⊗> B
  _<⊗_ : {A : Context} (p : is-structural-lhs A) (B : Type) → is-structural-lhs A <⊗ B

is-structural-lhs?_ : (A : Context) → Dec (is-structural-lhs A)
is-structural-lhs? []       = yes []
is-structural-lhs? A ⊗> B with is-structural-lhs? B
is-structural-lhs? A ⊗> _ | yes B = yes (A ⊗> B)
is-structural-lhs? A ⊗> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-structural-lhs A ⊗> B → is-structural-lhs B
        lem (A ⊗> B) = B
is-structural-lhs? A <⊗ B with is-structural-lhs? A
is-structural-lhs? _ <⊗ B | yes A = yes (A <⊗ B)
is-structural-lhs? _ <⊗ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-structural-lhs A <⊗ B → is-structural-lhs A
        lem (A <⊗ B) = A
is-structural-lhs? A ⇛> B = no (λ ())
is-structural-lhs? A ⇚> B = no (λ ())
is-structural-lhs? A ⊕> B = no (λ ())
is-structural-lhs? A ⇒> B = no (λ ())
is-structural-lhs? A ⇐> B = no (λ ())
is-structural-lhs? A <⇛ B = no (λ ())
is-structural-lhs? A <⇚ B = no (λ ())
is-structural-lhs? A <⊕ B = no (λ ())
is-structural-lhs? A <⇒ B = no (λ ())
is-structural-lhs? A <⇐ B = no (λ ())


infix 2 is-structural_ is-structural?_

data is-structural_ : JudgementContext → Set ℓ where
  _<⊢_ : {A : Context} (p : is-structural-lhs A) (B : Type) → is-structural (A <⊢ B)

is-structural?_ : (J : JudgementContext) → Dec (is-structural J)
is-structural? A <⊢ B with (is-structural-lhs? A)
is-structural? _ <⊢ B | yes A = yes (A <⊢ B)
is-structural? _ <⊢ B | no ¬A = no (¬A ∘ lem)
  where
    lem : ∀ {A B} → is-structural A <⊢ B → is-structural-lhs A
    lem (A <⊢ B) = A
is-structural? A ⊢> B = no (λ ())


-- Proofs regarding "input contexts", i.e. contexts whose type can be
-- seen as "consuming something".

infix 5 is-input-rhs_ is-input-rhs?_

data is-input-rhs_ : Context → Set ℓ where
  _⇐>_ : (A : Type) {B : Context} (p : is-structural-lhs B) → is-input-rhs A ⇐> B
  _<⇒_ : {A : Context} (p : is-structural-lhs A) (B : Type) → is-input-rhs A <⇒ B
  _⇒>_ : (A : Type) {B : Context} (p : is-input-rhs B) → is-input-rhs A ⇒> B
  _<⇐_ : {A : Context} (p : is-input-rhs A) (B : Type) → is-input-rhs A <⇐ B

is-input-rhs?_ : (A : Context) → Dec (is-input-rhs A)
is-input-rhs? []     = no (λ ())
is-input-rhs? A ⊗> B = no (λ ())
is-input-rhs? A ⇛> B = no (λ ())
is-input-rhs? A ⇚> B = no (λ ())
is-input-rhs? A ⊕> B = no (λ ())
is-input-rhs? A ⇒> B with (is-input-rhs? B)
is-input-rhs? A ⇒> _ | yes B = yes (A ⇒> B)
is-input-rhs? A ⇒> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-input-rhs A ⇒> B → is-input-rhs B
        lem (A ⇒> B) = B
is-input-rhs? A ⇐> B with (is-structural-lhs? B)
is-input-rhs? A ⇐> _ | yes B = yes (A ⇐> B)
is-input-rhs? A ⇐> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-input-rhs A ⇐> B → is-structural-lhs B
        lem (A ⇐> B) = B
is-input-rhs? A <⊗ B = no (λ ())
is-input-rhs? A <⇛ B = no (λ ())
is-input-rhs? A <⇚ B = no (λ ())
is-input-rhs? A <⊕ B = no (λ ())
is-input-rhs? A <⇒ B with (is-structural-lhs? A)
is-input-rhs? _ <⇒ B | yes A = yes (A <⇒ B)
is-input-rhs? _ <⇒ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-input-rhs A <⇒ B → is-structural-lhs A
        lem (A <⇒ B) = A
is-input-rhs? A <⇐ B with (is-input-rhs? A)
is-input-rhs? _ <⇐ B | yes A = yes (A <⇐ B)
is-input-rhs? _ <⇐ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-input-rhs A <⇐ B → is-input-rhs A
        lem (A <⇐ B) = A


infix 2 is-input_ is-input?_

data is-input_ : JudgementContext → Set ℓ where
  _<⊢_ : {A : Context} (p : is-structural-lhs A) (B : Type) → is-input A <⊢ B
  _⊢>_ : (A : Type) {B : Context} (p : is-input-rhs B) → is-input A ⊢> B

is-input?_ : (J : JudgementContext) → Dec (is-input J)
is-input? A <⊢ B with (is-structural-lhs? A)
is-input? _ <⊢ B | yes A = yes (A <⊢ B)
is-input? _ <⊢ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-input A <⊢ B → is-structural-lhs A
        lem (A <⊢ B) = A
is-input? A ⊢> B with (is-input-rhs? B)
is-input? A ⊢> _ | yes B = yes (A ⊢> B)
is-input? A ⊢> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-input A ⊢> B → is-input-rhs B
        lem (A ⊢> B) = B


-- Proofs regarding "output contexts", i.e. contexts whose type can be
-- seen as "producing something".

infix 5 is-output-rhs_ is-output-rhs?_

data is-output-rhs_ : Context → Set ℓ where
  []   : is-output-rhs []
  _⇒>_ : (A : Type) {B : Context} (p : is-output-rhs B) → is-output-rhs A ⇒> B
  _<⇐_ : {A : Context} (p : is-output-rhs A) (B : Type) → is-output-rhs A <⇐ B


is-output-rhs?_ : (A : Context) → Dec (is-output-rhs A)
is-output-rhs? [] = yes []
is-output-rhs? A ⊗> B = no (λ ())
is-output-rhs? A ⇛> B = no (λ ())
is-output-rhs? A ⇚> B = no (λ ())
is-output-rhs? A ⊕> B = no (λ ())
is-output-rhs? A ⇒> B with (is-output-rhs? B)
is-output-rhs? A ⇒> _ | yes B = yes (A ⇒> B)
is-output-rhs? A ⇒> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-output-rhs A ⇒> B → is-output-rhs B
        lem (A ⇒> B) = B
is-output-rhs? A ⇐> B = no (λ ())
is-output-rhs? A <⊗ B = no (λ ())
is-output-rhs? A <⇛ B = no (λ ())
is-output-rhs? A <⇚ B = no (λ ())
is-output-rhs? A <⊕ B = no (λ ())
is-output-rhs? A <⇒ B = no (λ ())
is-output-rhs? A <⇐ B with (is-output-rhs? A)
is-output-rhs? _ <⇐ B | yes A = yes (A <⇐ B)
is-output-rhs? _ <⇐ B | no ¬A = no (¬A ∘ lem)
  where lem : ∀ {A B} → is-output-rhs A <⇐ B → is-output-rhs A
        lem (A <⇐ B) = A


infix 2 is-output_ is-output?_

data is-output_ : JudgementContext → Set ℓ where
  _⊢>_ : (A : Type) {B : Context} (p : is-output-rhs B) → is-output A ⊢> B


is-output?_ : (J : JudgementContext) → Dec (is-output J)
is-output? A <⊢ B = no (λ ())
is-output? A ⊢> B with (is-output-rhs? B)
is-output? A ⊢> _ | yes B = yes (A ⊢> B)
is-output? A ⊢> _ | no ¬B = no (¬B ∘ lem)
  where lem : ∀ {A B} → is-output A ⊢> B → is-output-rhs B
        lem (A ⊢> B) = B
