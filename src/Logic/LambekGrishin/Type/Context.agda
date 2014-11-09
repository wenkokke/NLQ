------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Category using (Category; Functor; Monoids; Sets)
open import Algebra using (Monoid)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.LambekGrishin.Type.Context {ℓ} (Univ : Set ℓ) where


open import Logic.LambekGrishin.Type Univ renaming (module DecEq to DecEqType)


infixr 30 _⊗>_ _<⊗_ _⊕>_ _<⊕_
infixr 20 _⇛>_ _<⇛_ _⇒>_ _<⇒_
infixl 20 _⇚>_ _<⇚_ _⇐>_ _<⇐_


-- Contexts encode incomplete types with a single hole.
data Context : Set ℓ where

  []   : Context

  _⊗>_ : Type → Context → Context
  _⇛>_ : Type → Context → Context
  _⇚>_ : Type → Context → Context
  _⊕>_ : Type → Context → Context
  _⇒>_ : Type → Context → Context
  _⇐>_ : Type → Context → Context

  _<⊗_ : Context → Type → Context
  _<⇛_ : Context → Type → Context
  _<⇚_ : Context → Type → Context
  _<⊕_ : Context → Type → Context
  _<⇒_ : Context → Type → Context
  _<⇐_ : Context → Type → Context


-- Proofs which show that constructors of contexts (as all Agda
-- data-constructors) respect equality.

⊗>-injective : ∀ {A B C D} → A ⊗> B ≡ C ⊗> D → A ≡ C × B ≡ D
⊗>-injective refl = refl , refl

⇒>-injective : ∀ {A B C D} → A ⇒> B ≡ C ⇒> D → A ≡ C × B ≡ D
⇒>-injective refl = refl , refl

⇐>-injective : ∀ {A B C D} → A ⇐> B ≡ C ⇐> D → A ≡ C × B ≡ D
⇐>-injective refl = refl , refl

<⊗-injective : ∀ {A B C D} → A <⊗ B ≡ C <⊗ D → A ≡ C × B ≡ D
<⊗-injective refl = refl , refl

<⇒-injective : ∀ {A B C D} → A <⇒ B ≡ C <⇒ D → A ≡ C × B ≡ D
<⇒-injective refl = refl , refl

<⇐-injective : ∀ {A B C D} → A <⇐ B ≡ C <⇐ D → A ≡ C × B ≡ D
<⇐-injective refl = refl , refl

⊕>-injective : ∀ {A B C D} → A ⊕> B ≡ C ⊕> D → A ≡ C × B ≡ D
⊕>-injective refl = refl , refl

⇛>-injective : ∀ {A B C D} → A ⇛> B ≡ C ⇛> D → A ≡ C × B ≡ D
⇛>-injective refl = refl , refl

⇚>-injective : ∀ {A B C D} → A ⇚> B ≡ C ⇚> D → A ≡ C × B ≡ D
⇚>-injective refl = refl , refl

<⊕-injective : ∀ {A B C D} → A <⊕ B ≡ C <⊕ D → A ≡ C × B ≡ D
<⊕-injective refl = refl , refl

<⇛-injective : ∀ {A B C D} → A <⇛ B ≡ C <⇛ D → A ≡ C × B ≡ D
<⇛-injective refl = refl , refl

<⇚-injective : ∀ {A B C D} → A <⇚ B ≡ C <⇚ D → A ≡ C × B ≡ D
<⇚-injective refl = refl , refl


module Simple where

  -- Apply a context to a type by plugging the type into the context.
  _[_] : Context → Type → Type
  []       [ A ] = A
  (B ⊗> C) [ A ] = B ⊗ (C [ A ])
  (B ⇒> C) [ A ] = B ⇒ (C [ A ])
  (B ⇐> C) [ A ] = B ⇐ (C [ A ])
  (B ⊕> C) [ A ] = B ⊕ (C [ A ])
  (B ⇛> C) [ A ] = B ⇛ (C [ A ])
  (B ⇚> C) [ A ] = B ⇚ (C [ A ])
  (C <⊗ B) [ A ] = (C [ A ]) ⊗ B
  (C <⇒ B) [ A ] = (C [ A ]) ⇒ B
  (C <⇐ B) [ A ] = (C [ A ]) ⇐ B
  (C <⊕ B) [ A ] = (C [ A ]) ⊕ B
  (C <⇛ B) [ A ] = (C [ A ]) ⇛ B
  (C <⇚ B) [ A ] = (C [ A ]) ⇚ B

  -- Compose two contexts to form a new context.
  _<_> : Context → Context → Context
  []       < A > = A
  (B ⊗> C) < A > = B ⊗> (C < A >)
  (B ⇒> C) < A > = B ⇒> (C < A >)
  (B ⇐> C) < A > = B ⇐> (C < A >)
  (B ⊕> C) < A > = B ⊕> (C < A >)
  (B ⇛> C) < A > = B ⇛> (C < A >)
  (B ⇚> C) < A > = B ⇚> (C < A >)
  (C <⊗ B) < A > = (C < A >) <⊗ B
  (C <⇒ B) < A > = (C < A >) <⇒ B
  (C <⇐ B) < A > = (C < A >) <⇐ B
  (C <⊕ B) < A > = (C < A >) <⊕ B
  (C <⇛ B) < A > = (C < A >) <⇛ B
  (C <⇚ B) < A > = (C < A >) <⇚ B


  -- Lemma which shows how context composition `_<_>` and context
  -- application `_[_]` interact.
  <>-def : ∀ A B C → A < B > [ C ] ≡ A [ B [ C ] ]
  <>-def [] B C = refl
  <>-def (_ ⊗> A) B C rewrite <>-def A B C = refl
  <>-def (_ ⇒> A) B C rewrite <>-def A B C = refl
  <>-def (_ ⇐> A) B C rewrite <>-def A B C = refl
  <>-def (_ ⊕> A) B C rewrite <>-def A B C = refl
  <>-def (_ ⇛> A) B C rewrite <>-def A B C = refl
  <>-def (_ ⇚> A) B C rewrite <>-def A B C = refl
  <>-def (A <⊗ _) B C rewrite <>-def A B C = refl
  <>-def (A <⇒ _) B C rewrite <>-def A B C = refl
  <>-def (A <⇐ _) B C rewrite <>-def A B C = refl
  <>-def (A <⊕ _) B C rewrite <>-def A B C = refl
  <>-def (A <⇛ _) B C rewrite <>-def A B C = refl
  <>-def (A <⇚ _) B C rewrite <>-def A B C = refl


  -- Lemma which shows that context composition respects propositional
  -- equality.
  <>-cong : ∀ {Γ Δ Π Σ} → Γ ≡ Δ → Π ≡ Σ → Γ < Π > ≡ Δ < Σ >
  <>-cong Γ=Δ Π=Σ rewrite Γ=Δ | Π=Σ = refl


  -- Lemma which shows that the context composition function `_<_>` is
  -- associative.x
  <>-assoc : ∀ A B C → A < B > < C > ≡ A < B < C > >
  <>-assoc []       B C = refl
  <>-assoc (_ ⊗> A) B C rewrite <>-assoc A B C = refl
  <>-assoc (_ ⇒> A) B C rewrite <>-assoc A B C = refl
  <>-assoc (_ ⇐> A) B C rewrite <>-assoc A B C = refl
  <>-assoc (_ ⊕> A) B C rewrite <>-assoc A B C = refl
  <>-assoc (_ ⇛> A) B C rewrite <>-assoc A B C = refl
  <>-assoc (_ ⇚> A) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⊗ _) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⇒ _) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⇐ _) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⊕ _) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⇛ _) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⇚ _) B C rewrite <>-assoc A B C = refl


  -- Lemma which shows that `[]` is the identity element for the context
  -- composition function `_<_>`.
  <>-identityˡ : ∀ Γ → [] < Γ > ≡ Γ
  <>-identityˡ _ = refl

  <>-identityʳ : ∀ Γ → Γ < [] > ≡ Γ
  <>-identityʳ [] = refl
  <>-identityʳ (A ⊗> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (A ⇒> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (A ⇐> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (A ⊕> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (A ⇛> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (A ⇚> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⊗ A) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⇒ A) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⇐ A) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⊕ A) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⇛ A) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⇚ A) rewrite <>-identityʳ Γ = refl


-- Proof that `_<_>` and `[]` form a monoid over contexts.
instance
  monoid : Monoid _ _
  monoid = record
    { Carrier  = Context
    ; _≈_      = _≡_
    ; _∙_      = _<_>
    ; ε        = []
    ; isMonoid = record
      { identity    = (<>-identityˡ , <>-identityʳ)
      ; isSemigroup = record
        { isEquivalence = P.isEquivalence
        ; assoc         = <>-assoc
        ; ∙-cong        = <>-cong
        }
      }
    }
    where
      open Simple


-- Proof that `_[_]` forms a functor from contexts into types
functor : Functor (Monoids monoid) (Sets ℓ)
functor = record
  { F₀           = λ {tt → Type}
  ; F₁           = _[_]
  ; identity     = refl
  ; homomorphism = λ {_} {_} {_} {f} {g} → <>-def g f _
  ; F-resp-≈     = F-resp-≈
  }
  where
    open Simple
    F-resp-≈ : ∀ {A B} → A ≡ B → ∀ {C} → A [ C ] ≡ B [ C ]
    F-resp-≈ refl = refl


-- Proof that if the given universe has decidable equality, then so do contexts.
module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where

  open DecEqType _≟-Univ_

  infix 4 _≟-Context_

  _≟-Context_ : (Γ Δ : Context) → Dec (Γ ≡ Δ)
  []     ≟-Context []     = yes refl
  []     ≟-Context B ⊗> Δ = no (λ ())
  []     ≟-Context B ⇒> Δ = no (λ ())
  []     ≟-Context B ⇐> Δ = no (λ ())
  []     ≟-Context B ⊕> Δ = no (λ ())
  []     ≟-Context B ⇛> Δ = no (λ ())
  []     ≟-Context B ⇚> Δ = no (λ ())
  []     ≟-Context Δ <⊗ B = no (λ ())
  []     ≟-Context Δ <⇒ B = no (λ ())
  []     ≟-Context Δ <⇐ B = no (λ ())
  []     ≟-Context Δ <⊕ B = no (λ ())
  []     ≟-Context Δ <⇛ B = no (λ ())
  []     ≟-Context Δ <⇚ B = no (λ ())
  A ⊗> Γ ≟-Context []     = no (λ ())
  A ⇒> Γ ≟-Context []     = no (λ ())
  A ⇐> Γ ≟-Context []     = no (λ ())
  A ⊕> Γ ≟-Context []     = no (λ ())
  A ⇛> Γ ≟-Context []     = no (λ ())
  A ⇚> Γ ≟-Context []     = no (λ ())
  Γ <⊗ A ≟-Context []     = no (λ ())
  Γ <⇒ A ≟-Context []     = no (λ ())
  Γ <⇐ A ≟-Context []     = no (λ ())
  Γ <⊕ A ≟-Context []     = no (λ ())
  Γ <⇛ A ≟-Context []     = no (λ ())
  Γ <⇚ A ≟-Context []     = no (λ ())
  A ⊗> Γ ≟-Context B ⊗> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⊗>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⊗>-injective)
  A ⊗> Γ ≟-Context B ⇒> Δ = no (λ ())
  A ⊗> Γ ≟-Context B ⇐> Δ = no (λ ())
  A ⊗> Γ ≟-Context B ⊕> Δ = no (λ ())
  A ⊗> Γ ≟-Context B ⇛> Δ = no (λ ())
  A ⊗> Γ ≟-Context B ⇚> Δ = no (λ ())
  A ⊗> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⊗> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⊗> Γ ≟-Context Δ <⇐ B = no (λ ())
  A ⊗> Γ ≟-Context Δ <⊕ B = no (λ ())
  A ⊗> Γ ≟-Context Δ <⇛ B = no (λ ())
  A ⊗> Γ ≟-Context Δ <⇚ B = no (λ ())
  A ⇒> Γ ≟-Context B ⊗> Δ = no (λ ())
  A ⇒> Γ ≟-Context B ⇒> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⇒>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⇒>-injective)
  A ⇒> Γ ≟-Context B ⇐> Δ = no (λ ())
  A ⇒> Γ ≟-Context B ⊕> Δ = no (λ ())
  A ⇒> Γ ≟-Context B ⇛> Δ = no (λ ())
  A ⇒> Γ ≟-Context B ⇚> Δ = no (λ ())
  A ⇒> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⇒> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⇒> Γ ≟-Context Δ <⇐ B = no (λ ())
  A ⇒> Γ ≟-Context Δ <⊕ B = no (λ ())
  A ⇒> Γ ≟-Context Δ <⇛ B = no (λ ())
  A ⇒> Γ ≟-Context Δ <⇚ B = no (λ ())
  A ⇐> Γ ≟-Context B ⊗> Δ = no (λ ())
  A ⇐> Γ ≟-Context B ⇒> Δ = no (λ ())
  A ⇐> Γ ≟-Context B ⇐> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⇐>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⇐>-injective)
  A ⇐> Γ ≟-Context B ⊕> Δ = no (λ ())
  A ⇐> Γ ≟-Context B ⇛> Δ = no (λ ())
  A ⇐> Γ ≟-Context B ⇚> Δ = no (λ ())
  A ⇐> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⇐> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⇐> Γ ≟-Context Δ <⇐ B = no (λ ())
  A ⇐> Γ ≟-Context Δ <⊕ B = no (λ ())
  A ⇐> Γ ≟-Context Δ <⇛ B = no (λ ())
  A ⇐> Γ ≟-Context Δ <⇚ B = no (λ ())
  A ⊕> Γ ≟-Context B ⊗> Δ = no (λ ())
  A ⊕> Γ ≟-Context B ⇒> Δ = no (λ ())
  A ⊕> Γ ≟-Context B ⇐> Δ = no (λ ())
  A ⊕> Γ ≟-Context B ⊕> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⊕>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⊕>-injective)
  A ⊕> Γ ≟-Context B ⇛> Δ = no (λ ())
  A ⊕> Γ ≟-Context B ⇚> Δ = no (λ ())
  A ⊕> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⊕> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⊕> Γ ≟-Context Δ <⇐ B = no (λ ())
  A ⊕> Γ ≟-Context Δ <⊕ B = no (λ ())
  A ⊕> Γ ≟-Context Δ <⇛ B = no (λ ())
  A ⊕> Γ ≟-Context Δ <⇚ B = no (λ ())
  A ⇛> Γ ≟-Context B ⊗> Δ = no (λ ())
  A ⇛> Γ ≟-Context B ⇒> Δ = no (λ ())
  A ⇛> Γ ≟-Context B ⇐> Δ = no (λ ())
  A ⇛> Γ ≟-Context B ⊕> Δ = no (λ ())
  A ⇛> Γ ≟-Context B ⇛> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⇛>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⇛>-injective)
  A ⇛> Γ ≟-Context B ⇚> Δ = no (λ ())
  A ⇛> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⇛> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⇛> Γ ≟-Context Δ <⇐ B = no (λ ())
  A ⇛> Γ ≟-Context Δ <⊕ B = no (λ ())
  A ⇛> Γ ≟-Context Δ <⇛ B = no (λ ())
  A ⇛> Γ ≟-Context Δ <⇚ B = no (λ ())
  A ⇚> Γ ≟-Context B ⊗> Δ = no (λ ())
  A ⇚> Γ ≟-Context B ⇒> Δ = no (λ ())
  A ⇚> Γ ≟-Context B ⇐> Δ = no (λ ())
  A ⇚> Γ ≟-Context B ⊕> Δ = no (λ ())
  A ⇚> Γ ≟-Context B ⇛> Δ = no (λ ())
  A ⇚> Γ ≟-Context B ⇚> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⇚>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⇚>-injective)
  A ⇚> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⇚> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⇚> Γ ≟-Context Δ <⇐ B = no (λ ())
  A ⇚> Γ ≟-Context Δ <⊕ B = no (λ ())
  A ⇚> Γ ≟-Context Δ <⇛ B = no (λ ())
  A ⇚> Γ ≟-Context Δ <⇚ B = no (λ ())
  Γ <⊗ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⊗ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⊗ A ≟-Context B ⇐> Δ = no (λ ())
  Γ <⊗ A ≟-Context B ⊕> Δ = no (λ ())
  Γ <⊗ A ≟-Context B ⇛> Δ = no (λ ())
  Γ <⊗ A ≟-Context B ⇚> Δ = no (λ ())
  Γ <⊗ A ≟-Context Δ <⊗ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⊗-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⊗-injective)
  Γ <⊗ A ≟-Context Δ <⇒ B = no (λ ())
  Γ <⊗ A ≟-Context Δ <⇐ B = no (λ ())
  Γ <⊗ A ≟-Context Δ <⊕ B = no (λ ())
  Γ <⊗ A ≟-Context Δ <⇛ B = no (λ ())
  Γ <⊗ A ≟-Context Δ <⇚ B = no (λ ())
  Γ <⇒ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⇒ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⇒ A ≟-Context B ⇐> Δ = no (λ ())
  Γ <⇒ A ≟-Context B ⊕> Δ = no (λ ())
  Γ <⇒ A ≟-Context B ⇛> Δ = no (λ ())
  Γ <⇒ A ≟-Context B ⇚> Δ = no (λ ())
  Γ <⇒ A ≟-Context Δ <⊗ B = no (λ ())
  Γ <⇒ A ≟-Context Δ <⇒ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⇒-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⇒-injective)
  Γ <⇒ A ≟-Context Δ <⇐ B = no (λ ())
  Γ <⇒ A ≟-Context Δ <⊕ B = no (λ ())
  Γ <⇒ A ≟-Context Δ <⇛ B = no (λ ())
  Γ <⇒ A ≟-Context Δ <⇚ B = no (λ ())
  Γ <⇐ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⇐ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⇐ A ≟-Context B ⇐> Δ = no (λ ())
  Γ <⇐ A ≟-Context B ⊕> Δ = no (λ ())
  Γ <⇐ A ≟-Context B ⇛> Δ = no (λ ())
  Γ <⇐ A ≟-Context B ⇚> Δ = no (λ ())
  Γ <⇐ A ≟-Context Δ <⊗ B = no (λ ())
  Γ <⇐ A ≟-Context Δ <⇒ B = no (λ ())
  Γ <⇐ A ≟-Context Δ <⇐ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⇐-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⇐-injective)
  Γ <⇐ A ≟-Context Δ <⊕ B = no (λ ())
  Γ <⇐ A ≟-Context Δ <⇛ B = no (λ ())
  Γ <⇐ A ≟-Context Δ <⇚ B = no (λ ())
  Γ <⊕ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⊕ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⊕ A ≟-Context B ⇐> Δ = no (λ ())
  Γ <⊕ A ≟-Context B ⊕> Δ = no (λ ())
  Γ <⊕ A ≟-Context B ⇛> Δ = no (λ ())
  Γ <⊕ A ≟-Context B ⇚> Δ = no (λ ())
  Γ <⊕ A ≟-Context Δ <⊗ B = no (λ ())
  Γ <⊕ A ≟-Context Δ <⇒ B = no (λ ())
  Γ <⊕ A ≟-Context Δ <⇐ B = no (λ ())
  Γ <⊕ A ≟-Context Δ <⊕ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⊕-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⊕-injective)
  Γ <⊕ A ≟-Context Δ <⇛ B = no (λ ())
  Γ <⊕ A ≟-Context Δ <⇚ B = no (λ ())
  Γ <⇛ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⇛ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⇛ A ≟-Context B ⇐> Δ = no (λ ())
  Γ <⇛ A ≟-Context B ⊕> Δ = no (λ ())
  Γ <⇛ A ≟-Context B ⇛> Δ = no (λ ())
  Γ <⇛ A ≟-Context B ⇚> Δ = no (λ ())
  Γ <⇛ A ≟-Context Δ <⊗ B = no (λ ())
  Γ <⇛ A ≟-Context Δ <⇒ B = no (λ ())
  Γ <⇛ A ≟-Context Δ <⇐ B = no (λ ())
  Γ <⇛ A ≟-Context Δ <⊕ B = no (λ ())
  Γ <⇛ A ≟-Context Δ <⇛ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⇛-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⇛-injective)
  Γ <⇛ A ≟-Context Δ <⇚ B = no (λ ())
  Γ <⇚ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⇚ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⇚ A ≟-Context B ⇐> Δ = no (λ ())
  Γ <⇚ A ≟-Context B ⊕> Δ = no (λ ())
  Γ <⇚ A ≟-Context B ⇛> Δ = no (λ ())
  Γ <⇚ A ≟-Context B ⇚> Δ = no (λ ())
  Γ <⇚ A ≟-Context Δ <⊗ B = no (λ ())
  Γ <⇚ A ≟-Context Δ <⇒ B = no (λ ())
  Γ <⇚ A ≟-Context Δ <⇐ B = no (λ ())
  Γ <⇚ A ≟-Context Δ <⊕ B = no (λ ())
  Γ <⇚ A ≟-Context Δ <⇛ B = no (λ ())
  Γ <⇚ A ≟-Context Δ <⇚ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⇚-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⇚-injective)
