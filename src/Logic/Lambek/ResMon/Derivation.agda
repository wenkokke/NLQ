------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Categories using (Category; Functor; Sets)
open import Function using (_∘_)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Lambek.ResMon.Derivation {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type Univ
open import Logic.Lambek.ResMon.Base Univ
open import Logic.Lambek.Judgement Univ


infix 3 NL_⋯_


data NL_⋯_ : (I J : Judgement) → Set ℓ where
  []     : ∀ {J}         → NL J ⋯ J

  -- rules for residuation and monotonicity
  res-⇒⊗ : ∀ {J A B C}   → NL J ⋯ B ⊢ A ⇒ C → NL J ⋯ A ⊗ B ⊢ C
  res-⊗⇒ : ∀ {J A B C}   → NL J ⋯ A ⊗ B ⊢ C → NL J ⋯ B ⊢ A ⇒ C
  res-⇐⊗ : ∀ {J A B C}   → NL J ⋯ A ⊢ C ⇐ B → NL J ⋯ A ⊗ B ⊢ C
  res-⊗⇐ : ∀ {J A B C}   → NL J ⋯ A ⊗ B ⊢ C → NL J ⋯ A ⊢ C ⇐ B
  mon-⊗ᴸ : ∀ {J A B C D} → NL J ⋯ A ⊢ B → NL C ⊢ D → NL J ⋯ A ⊗ C ⊢ B ⊗ D
  mon-⊗ᴿ : ∀ {J A B C D} → NL A ⊢ B → NL J ⋯ C ⊢ D → NL J ⋯ A ⊗ C ⊢ B ⊗ D
  mon-⇒ᴸ : ∀ {J A B C D} → NL J ⋯ A ⊢ B → NL C ⊢ D → NL J ⋯ B ⇒ C ⊢ A ⇒ D
  mon-⇒ᴿ : ∀ {J A B C D} → NL A ⊢ B → NL J ⋯ C ⊢ D → NL J ⋯ B ⇒ C ⊢ A ⇒ D
  mon-⇐ᴸ : ∀ {J A B C D} → NL J ⋯ A ⊢ B → NL C ⊢ D → NL J ⋯ A ⇐ D ⊢ B ⇐ C
  mon-⇐ᴿ : ∀ {J A B C D} → NL A ⊢ B → NL J ⋯ C ⊢ D → NL J ⋯ A ⇐ D ⊢ B ⇐ C

  -- rules for co-residuation and co-monotonicity
  -- grishin distributives
-- We can also define the property of being empty for a proof context;
-- the reason we do this is because we cannot directly use decidable
-- equality due to the fact that [] forces the types of A and C and B
-- and D to be equal.

infix 5 is-[]_ is-[]?_

data is-[]_ : {I J : Judgement} (f : NL I ⋯ J) → Set ℓ where
  [] : ∀ {I} → is-[] ([] {I})

is-[]?_ : ∀ {I J} (f : NL I ⋯ J) → Dec (is-[] f)
is-[]? []         = yes []
is-[]? res-⇒⊗ _   = no (λ ())
is-[]? res-⊗⇒ _   = no (λ ())
is-[]? res-⇐⊗ _   = no (λ ())
is-[]? res-⊗⇐ _   = no (λ ())
is-[]? mon-⊗ᴸ _ _ = no (λ ())
is-[]? mon-⊗ᴿ _ _ = no (λ ())
is-[]? mon-⇒ᴸ _ _ = no (λ ())
is-[]? mon-⇒ᴿ _ _ = no (λ ())
is-[]? mon-⇐ᴸ _ _ = no (λ ())
is-[]? mon-⇐ᴿ _ _ = no (λ ())
module Simple where


  -- Proof contexts can be applied, by inserting the proof into the hole
  -- in the proof context.
  _[_] : ∀ {I J} → NL I ⋯ J → NL I → NL J
  []           [ g ] = g
  res-⇒⊗ f     [ g ] = res-⇒⊗ (f  [ g ])
  res-⊗⇒ f     [ g ] = res-⊗⇒ (f  [ g ])
  res-⇐⊗ f     [ g ] = res-⇐⊗ (f  [ g ])
  res-⊗⇐ f     [ g ] = res-⊗⇐ (f  [ g ])
  mon-⊗ᴸ f₁ f₂ [ g ] = mon-⊗  (f₁ [ g ])  f₂
  mon-⊗ᴿ f₁ f₂ [ g ] = mon-⊗   f₁        (f₂ [ g ])
  mon-⇒ᴸ f₁ f₂ [ g ] = mon-⇒  (f₁ [ g ])  f₂
  mon-⇒ᴿ f₁ f₂ [ g ] = mon-⇒   f₁        (f₂ [ g ])
  mon-⇐ᴸ f₁ f₂ [ g ] = mon-⇐  (f₁ [ g ])  f₂
  mon-⇐ᴿ f₁ f₂ [ g ] = mon-⇐   f₁        (f₂ [ g ])
  -- Proof contexts can also be composed, simply by plugging the one
  -- proof context into the hole in the other proof context.
  _<_> : ∀ {I J K} (f : NL J ⋯ K) (g : NL I ⋯ J) → NL I ⋯ K
  []           < g > = g
  res-⇒⊗ f     < g > = res-⇒⊗ (f  < g >)
  res-⊗⇒ f     < g > = res-⊗⇒ (f  < g >)
  res-⇐⊗ f     < g > = res-⇐⊗ (f  < g >)
  res-⊗⇐ f     < g > = res-⊗⇐ (f  < g >)
  mon-⊗ᴸ f₁ f₂ < g > = mon-⊗ᴸ (f₁ < g >)  f₂
  mon-⊗ᴿ f₁ f₂ < g > = mon-⊗ᴿ  f₁        (f₂ < g >)
  mon-⇒ᴸ f₁ f₂ < g > = mon-⇒ᴸ (f₁ < g >)  f₂
  mon-⇒ᴿ f₁ f₂ < g > = mon-⇒ᴿ  f₁        (f₂ < g >)
  mon-⇐ᴸ f₁ f₂ < g > = mon-⇐ᴸ (f₁ < g >)  f₂
  mon-⇐ᴿ f₁ f₂ < g > = mon-⇐ᴿ  f₁        (f₂ < g >)
  -- We can also show that proof context composition distributes over
  -- proof context application.
  <>-def : ∀ {I J K} (f : NL J ⋯ K) (g : NL I ⋯ J) (h : NL I)
         → (f < g >) [ h ] ≡ f [ g [ h ] ]
  <>-def []             g h = refl
  <>-def (res-⇒⊗ f)     g h rewrite <>-def f  g h = refl
  <>-def (res-⊗⇒ f)     g h rewrite <>-def f  g h = refl
  <>-def (res-⇐⊗ f)     g h rewrite <>-def f  g h = refl
  <>-def (res-⊗⇐ f)     g h rewrite <>-def f  g h = refl
  <>-def (mon-⊗ᴸ f₁ f₂) g h rewrite <>-def f₁ g h = refl
  <>-def (mon-⊗ᴿ f₁ f₂) g h rewrite <>-def f₂ g h = refl
  <>-def (mon-⇒ᴸ f₁ f₂) g h rewrite <>-def f₁ g h = refl
  <>-def (mon-⇒ᴿ f₁ f₂) g h rewrite <>-def f₂ g h = refl
  <>-def (mon-⇐ᴸ f₁ f₂) g h rewrite <>-def f₁ g h = refl
  <>-def (mon-⇐ᴿ f₁ f₂) g h rewrite <>-def f₂ g h = refl
  <>-assoc : ∀ {A B C D} (f : NL C ⋯ D) (g : NL B ⋯ C) (h : NL A ⋯ B)
           → (f < g >) < h > ≡ f < g < h > >
  <>-assoc []             g h = refl
  <>-assoc (res-⇒⊗ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (res-⊗⇒ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (res-⇐⊗ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (res-⊗⇐ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (mon-⊗ᴸ f₁ f₂) g h rewrite <>-assoc f₁ g h = refl
  <>-assoc (mon-⊗ᴿ f₁ f₂) g h rewrite <>-assoc f₂ g h = refl
  <>-assoc (mon-⇒ᴸ f₁ f₂) g h rewrite <>-assoc f₁ g h = refl
  <>-assoc (mon-⇒ᴿ f₁ f₂) g h rewrite <>-assoc f₂ g h = refl
  <>-assoc (mon-⇐ᴸ f₁ f₂) g h rewrite <>-assoc f₁ g h = refl
  <>-assoc (mon-⇐ᴿ f₁ f₂) g h rewrite <>-assoc f₂ g h = refl
  <>-identityˡ : ∀ {A B} (f : NL A ⋯ B) → [] < f > ≡ f
  <>-identityˡ _ = refl

  <>-identityʳ : ∀ {A B} (f : NL A ⋯ B) → f < [] > ≡ f
  <>-identityʳ []             = refl
  <>-identityʳ (mon-⊗ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (mon-⊗ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (mon-⇒ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (mon-⇒ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (mon-⇐ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (mon-⇐ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (res-⇒⊗ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (res-⊗⇒ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (res-⇐⊗ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (res-⊗⇐ f)     rewrite <>-identityʳ f  = refl
  <>-resp-≡ : ∀ {A B C} {x y : NL B ⋯ C} {z w : NL A ⋯ B}
            → x ≡ y → z ≡ w → x < z > ≡ y < w >
  <>-resp-≡ p₁ p₂ rewrite p₁ | p₂ = refl


-- Proof that derivations form a category
instance
  category : Category _ _ _
  category = record
    { Obj           = Judgement
    ; Hom           = NL_⋯_
    ; ε             = []
    ; _∙_           = _<_>
    ; _≈_           = _≡_
    ; assoc         = λ {_} {_} {_} {_} {x} {y} {z} → <>-assoc x y z
    ; identityˡ     = <>-identityˡ _
    ; identityʳ     = <>-identityʳ _
    ; ∙-resp-≈      = <>-resp-≡
    ; isEquivalence = P.isEquivalence
    }
    where open Simple

instance
  functor : Functor category (Sets ℓ)
  functor = record
    { F₀           = NL_
    ; F₁           = _[_]
    ; identity     = refl
    ; homomorphism = λ {_} {_} {_} {f} {g} → <>-def g f _
    ; F-resp-≈     = F-resp-≈
    }
    where
      open Simple
      F-resp-≈ : ∀ {I J} {f g : NL I ⋯ J} → f ≡ g → ∀ {x} → f [ x ] ≡ g [ x ]
      F-resp-≈ refl = refl
