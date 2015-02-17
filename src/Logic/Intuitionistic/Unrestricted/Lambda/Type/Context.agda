------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level                                      using (zero)
open import Categories.Agda                            using (Sets)
open import Categories.Category                        using (Category)
open import Categories.Functor                         using (Functor)
open import Algebra                                    using (Monoid)
open import Function                                   using (_∘_)
open import Data.Unit                                  using (⊤; tt)
open import Data.Nat                                   using (decTotalOrder; z≤n; s≤s)
open import Data.Nat.Properties as NatProps            using (strictTotalOrder; ≤-step; n≤m+n; m≤m+n; _+-mono_)
open import Data.Empty                                 using (⊥; ⊥-elim)
open import Data.Product                               using (∃₂; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid; module DecTotalOrder; module StrictTotalOrder)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl; cong)


module Logic.Intuitionistic.Unrestricted.Lambda.Type.Context {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Unrestricted.Lambda.Type            Univ renaming (module DecEq to TypeDecEq)
open import Logic.Intuitionistic.Unrestricted.Lambda.Type.Complexity Univ
open DecTotalOrder decTotalOrder using (_≤_) renaming (refl to ≤-refl; trans to ≤-trans)
open StrictTotalOrder strictTotalOrder using (_<_) renaming (irrefl to <-irrefl; trans to <-trans)


infixr 30 _⊗>_ _<⊗_
infixr 20 _⇒>_ _<⇒_
-- Contexts encode incomplete types with a single hole.
data Context : Set ℓ where

  []   : Context

  _⊗>_ : Type → Context → Context
  _⇒>_ : Type → Context → Context
  _<⊗_ : Context → Type → Context
  _<⇒_ : Context → Type → Context
-- Proofs which show that constructors of contexts (as all Agda
-- data-constructors) respect equality.

⊗>-injective : ∀ {A B C D} → A ⊗> B ≡ C ⊗> D → A ≡ C × B ≡ D
⊗>-injective refl = refl , refl

⇒>-injective : ∀ {A B C D} → A ⇒> B ≡ C ⇒> D → A ≡ C × B ≡ D
⇒>-injective refl = refl , refl

<⊗-injective : ∀ {A B C D} → A <⊗ B ≡ C <⊗ D → A ≡ C × B ≡ D
<⊗-injective refl = refl , refl

<⇒-injective : ∀ {A B C D} → A <⇒ B ≡ C <⇒ D → A ≡ C × B ≡ D
<⇒-injective refl = refl , refl


module Simple where

  infix 50 _[_] _<_>

  -- Apply a context to a type by plugging the type into the context.
  _[_] : Context → Type → Type
  []       [ A ] = A
  (B ⊗> C) [ A ] = B ⊗ (C [ A ])
  (B ⇒> C) [ A ] = B ⇒ (C [ A ])
  (C <⊗ B) [ A ] = (C [ A ]) ⊗ B
  (C <⇒ B) [ A ] = (C [ A ]) ⇒ B
  -- Compose two contexts to form a new context.
  _<_> : Context → Context → Context
  []       < A > = A
  (B ⊗> C) < A > = B ⊗> (C < A >)
  (B ⇒> C) < A > = B ⇒> (C < A >)
  (C <⊗ B) < A > = (C < A >) <⊗ B
  (C <⇒ B) < A > = (C < A >) <⇒ B
  -- Lemma which shows that `_[_]` respects propositional equality
  []-resp-≡ : ∀ Ξ {A B} → A ≡ B → Ξ [ A ] ≡ Ξ [ B ]
  []-resp-≡ Ξ p rewrite p = refl


  -- Lemma which shows how context composition `_<_>` and context
  -- application `_[_]` interact.
  <>-def : ∀ A B C → A < B > [ C ] ≡ A [ B [ C ] ]
  <>-def [] B C = refl
  <>-def (_ ⊗> A) B C rewrite <>-def A B C = refl
  <>-def (_ ⇒> A) B C rewrite <>-def A B C = refl
  <>-def (A <⊗ _) B C rewrite <>-def A B C = refl
  <>-def (A <⇒ _) B C rewrite <>-def A B C = refl
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
  <>-assoc (A <⊗ _) B C rewrite <>-assoc A B C = refl
  <>-assoc (A <⇒ _) B C rewrite <>-assoc A B C = refl
  -- Lemma which shows that `[]` is the identity element for the context
  -- composition function `_<_>`.
  <>-identityˡ : ∀ Γ → [] < Γ > ≡ Γ
  <>-identityˡ _ = refl

  <>-identityʳ : ∀ Γ → Γ < [] > ≡ Γ
  <>-identityʳ [] = refl
  <>-identityʳ (A ⊗> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (A ⇒> Γ) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⊗ A) rewrite <>-identityʳ Γ = refl
  <>-identityʳ (Γ <⇒ A) rewrite <>-identityʳ Γ = refl
open Simple

-- Contexts can be unfolded if something is known about the type their
-- application results in
⊗-unfold : ∀ {Χ A C D}
         → Χ ≢ []
         → Χ [ A ] ≡ C ⊗ D
         → ∃₂ (λ Χ′ B → Χ ≡ B ⊗> Χ′ ⊎ Χ ≡ Χ′ <⊗ B)
⊗-unfold {[]}     Χ≠[] _ = ⊥-elim (Χ≠[] refl)
⊗-unfold {B ⊗> Χ} _ _ = Χ , B , inj₁ refl
⊗-unfold {Χ <⊗ B} _ _ = Χ , B , inj₂ refl
⊗-unfold {B ⇒> Χ} _ ()
⊗-unfold {Χ <⇒ B} _ ()
⇒-unfold : ∀ {Χ A C D}
         → Χ ≢ []
         → Χ [ A ] ≡ C ⇒ D
         → ∃₂ (λ Χ′ B → Χ ≡ B ⇒> Χ′ ⊎ Χ ≡ Χ′ <⇒ B)
⇒-unfold {[]}     Χ≠[] _ = ⊥-elim (Χ≠[] refl)
⇒-unfold {B ⊗> Χ} _ ()
⇒-unfold {Χ <⊗ B} _ ()
⇒-unfold {B ⇒> Χ} _ _ = Χ , B , inj₁ refl
⇒-unfold {Χ <⇒ B} _ _ = Χ , B , inj₂ refl
-- Simple decision procedure which checks if a context is the empty
-- context (superseded by the full decidable equality below, but
-- doesn't require a decidable equality on universes).
is-[]? : (A : Context) → Dec (A ≡ [])
is-[]? []       = yes refl
is-[]? (_ ⊗> _) = no (λ ())
is-[]? (_ ⇒> _) = no (λ ())
is-[]? (_ <⊗ _) = no (λ ())
is-[]? (_ <⇒ _) = no (λ ())
-- Lemma which shows that if a context is not empty, then applying it
-- to a type may never result in an elementary type.
Γ≠[]→elB≠Γ[A] : ∀ {A B} Γ → Γ ≢ [] → el B ≢ Γ [ A ]
Γ≠[]→elB≠Γ[A] [] Γ≠[] p = Γ≠[] refl
Γ≠[]→elB≠Γ[A] (_ ⊗> Γ) Γ≠[] ()
Γ≠[]→elB≠Γ[A] (Γ <⊗ _) Γ≠[] ()
Γ≠[]→elB≠Γ[A] (_ ⇒> Γ) Γ≠[] ()
Γ≠[]→elB≠Γ[A] (Γ <⇒ _) Γ≠[] ()
-- Lemma which shows that if a context is not empty, then wrapping it
-- around another context will always result in a non-empty context.
Δ≠[]→Δ<Γ>≠[] : ∀ Γ Δ → Δ ≢ [] → Δ < Γ > ≢ []
Δ≠[]→Δ<Γ>≠[] Γ [] Δ≠[] _ = Δ≠[] refl
Δ≠[]→Δ<Γ>≠[] Γ (_ ⊗> Δ) Δ≠[] ()
Δ≠[]→Δ<Γ>≠[] Γ (Δ <⊗ _) Δ≠[] ()
Δ≠[]→Δ<Γ>≠[] Γ (_ ⇒> Δ) Δ≠[] ()
Δ≠[]→Δ<Γ>≠[] Γ (Δ <⇒ _) Δ≠[] ()
-- Lemma which shows that if a context is not empty, then wrapping
-- another context around it will always result in a non-empty
-- context.
Γ≠[]→Δ<Γ>≠[] : ∀ Γ Δ → Γ ≢ [] → Δ < Γ > ≢ []
Γ≠[]→Δ<Γ>≠[] Γ    []    Γ≠[] = Γ≠[]
Γ≠[]→Δ<Γ>≠[] Γ (A ⊗> Δ) Γ≠[] = λ ()
Γ≠[]→Δ<Γ>≠[] Γ (A ⇒> Δ) Γ≠[] = λ ()
Γ≠[]→Δ<Γ>≠[] Γ (Δ <⊗ A) Γ≠[] = λ ()
Γ≠[]→Δ<Γ>≠[] Γ (Δ <⇒ A) Γ≠[] = λ ()
-- Lemma which shows that the complexity of a type embedded in a
-- context must always be greater or equal to the complexity of that
-- type itself.
A≤Γ[A] : ∀ A Γ → ⌈ A ⌉ ≤ ⌈ Γ [ A ] ⌉
A≤Γ[A] A [] = ≤-refl
A≤Γ[A] A (B ⊗> Γ) = ≤-step (≤-trans (A≤Γ[A] A Γ) (n≤m+n ⌈ B ⌉ ⌈ Γ [ A ] ⌉))
A≤Γ[A] A (Γ <⊗ B) = ≤-step (≤-trans (A≤Γ[A] A Γ) (m≤m+n ⌈ Γ [ A ] ⌉ ⌈ B ⌉))
A≤Γ[A] A (B ⇒> Γ) = ≤-step (≤-trans (A≤Γ[A] A Γ) (n≤m+n ⌈ B ⌉ ⌈ Γ [ A ] ⌉))
A≤Γ[A] A (Γ <⇒ B) = ≤-step (≤-trans (A≤Γ[A] A Γ) (m≤m+n ⌈ Γ [ A ] ⌉ ⌈ B ⌉))
-- Lemma which shows that if a context is not empty, then the
-- complexity of a type embedded in it must always be greater than the
-- complexity of that type itself.
Γ≠[]→A<Γ[A] : ∀ A Γ → Γ ≢ [] → ⌈ A ⌉ < ⌈ Γ [ A ] ⌉
Γ≠[]→A<Γ[A] A [] Γ≠[] = ⊥-elim (Γ≠[] refl)
Γ≠[]→A<Γ[A] A (B ⊗> Γ) _ = s≤s (≤-trans (A≤Γ[A] A Γ) (n≤m+n ⌈ B ⌉ ⌈ Γ [ A ] ⌉))
Γ≠[]→A<Γ[A] A (Γ <⊗ B) _ = s≤s (≤-trans (A≤Γ[A] A Γ) (m≤m+n ⌈ Γ [ A ] ⌉ ⌈ B ⌉))
Γ≠[]→A<Γ[A] A (B ⇒> Γ) _ = s≤s (≤-trans (A≤Γ[A] A Γ) (n≤m+n ⌈ B ⌉ ⌈ Γ [ A ] ⌉))
Γ≠[]→A<Γ[A] A (Γ <⇒ B) _ = s≤s (≤-trans (A≤Γ[A] A Γ) (m≤m+n ⌈ Γ [ A ] ⌉ ⌈ B ⌉))
-- Lemma which shows that if a context is not empty, the embedding of
-- a type in it cannot be equal to the type itself.
Γ≠[]→A≠Γ[A] : ∀ A Γ → Γ ≢ [] → A ≢ Γ [ A ]
Γ≠[]→A≠Γ[A] A Γ Γ≠[] p = <-irrefl A=Γ[A] A<Γ[A]
  where
    A=Γ[A] = cong ⌈_⌉ p
    A<Γ[A] = Γ≠[]→A<Γ[A] A Γ Γ≠[]


-- Lemma which shows that if the embedding of a type in a context is
-- equal to that type itself, then the context must be empty.
A=Γ[A]→Γ=[] : ∀ A Γ → A ≡ Γ [ A ] → Γ ≡ []
A=Γ[A]→Γ=[] A Γ A=Γ[A] with is-[]? Γ
... | yes Γ=[] = Γ=[]
... | no  Γ≠[] = ⊥-elim (Γ≠[]→A≠Γ[A] A Γ Γ≠[] A=Γ[A])


-- Proof that `_<_>` and `[]` form a monoid over contexts.
instance
  monoid : Monoid ℓ ℓ
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
    where open Simple


-- Proof that contexts also form a category
instance
  category : Category zero ℓ ℓ
  category = record
    { Obj          = ⊤
    ; _⇒_          = λ {tt tt → Context}
    ; _≡_          = _≡_
    ; id           = []
    ; _∘_          = _<_>
    ; assoc        = λ {_}{_}{_}{_}{f}{g}{h} → <>-assoc h g f
    ; identityˡ    = <>-identityˡ _
    ; identityʳ    = <>-identityʳ _
    ; equiv        = P.isEquivalence
    ; ∘-resp-≡     = <>-cong
    }
    where open Simple


-- Proof that `_[_]` forms a functor from contexts into types
instance
  functor : Functor category (Sets ℓ)
  functor = record
    { F₀           = λ {tt → Type}
    ; F₁           = _[_]
    ; identity     = refl
    ; homomorphism = λ {_}{_}{_}{f}{g}{x} → <>-def g f x
    ; F-resp-≡     = F-resp-≡
    }
    where
      open Simple
      F-resp-≡ : ∀ {A B} → A ≡ B → ∀ {C} → A [ C ] ≡ B [ C ]
      F-resp-≡ refl = refl


-- Proof that if the given universe has decidable equality, then so do contexts.
module DecEq (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where

  open TypeDecEq _≟-Univ_ using (_≟-Type_)

  infix 4 _≟-Context_

  _≟-Context_ : (Γ Δ : Context) → Dec (Γ ≡ Δ)
  []     ≟-Context []     = yes refl
  []     ≟-Context B ⊗> Δ = no (λ ())
  []     ≟-Context B ⇒> Δ = no (λ ())
  []     ≟-Context Δ <⊗ B = no (λ ())
  []     ≟-Context Δ <⇒ B = no (λ ())
  A ⊗> Γ ≟-Context []     = no (λ ())
  A ⇒> Γ ≟-Context []     = no (λ ())
  Γ <⊗ A ≟-Context []     = no (λ ())
  Γ <⇒ A ≟-Context []     = no (λ ())
  A ⊗> Γ ≟-Context B ⊗> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⊗>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⊗>-injective)
  A ⊗> Γ ≟-Context B ⇒> Δ = no (λ ())
  A ⊗> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⊗> Γ ≟-Context Δ <⇒ B = no (λ ())
  A ⇒> Γ ≟-Context B ⊗> Δ = no (λ ())
  A ⇒> Γ ≟-Context B ⇒> Δ with (A ≟-Type B) | (Γ ≟-Context Δ)
  ... | yes A≡B | yes Γ≡Δ rewrite A≡B | Γ≡Δ = yes refl
  ... | no  A≢B | _       = no (A≢B ∘ proj₁ ∘ ⇒>-injective)
  ... | _       | no  Γ≢Δ = no (Γ≢Δ ∘ proj₂ ∘ ⇒>-injective)
  A ⇒> Γ ≟-Context Δ <⊗ B = no (λ ())
  A ⇒> Γ ≟-Context Δ <⇒ B = no (λ ())
  Γ <⊗ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⊗ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⊗ A ≟-Context Δ <⊗ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⊗-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⊗-injective)
  Γ <⊗ A ≟-Context Δ <⇒ B = no (λ ())
  Γ <⇒ A ≟-Context B ⊗> Δ = no (λ ())
  Γ <⇒ A ≟-Context B ⇒> Δ = no (λ ())
  Γ <⇒ A ≟-Context Δ <⊗ B = no (λ ())
  Γ <⇒ A ≟-Context Δ <⇒ B with (Γ ≟-Context Δ) | (A ≟-Type B)
  ... | yes Γ≡Δ | yes A≡B rewrite Γ≡Δ | A≡B = yes refl
  ... | no  Γ≢Δ | _       = no (Γ≢Δ ∘ proj₁ ∘ <⇒-injective)
  ... | _       | no  A≢B = no (A≢B ∘ proj₂ ∘ <⇒-injective)
  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Context_
