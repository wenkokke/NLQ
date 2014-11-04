------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Category using (Category; Functor; set→category)
open import Function using (_∘_)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Lambek.ResMon.Derivation {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ
open import Logic.Lambek.Type Univ
open import Logic.Judgement Type Type
open import Logic.Lambek.ResMon.Base Univ


infix 3 NL_⋯_


data NL_⋯_ : (I J : Judgement) → Set ℓ where
  []     : ∀ {J}         → NL J ⋯ J
  mon-⊗ᴸ : ∀ {J A B C D} → NL J ⋯ A ⊢ B → NL C ⊢ D → NL J ⋯ A ⊗ C ⊢ B ⊗ D
  mon-⊗ᴿ : ∀ {J A B C D} → NL A ⊢ B → NL J ⋯ C ⊢ D → NL J ⋯ A ⊗ C ⊢ B ⊗ D
  mon-⇒ᴸ : ∀ {J A B C D} → NL J ⋯ A ⊢ B → NL C ⊢ D → NL J ⋯ B ⇒ C ⊢ A ⇒ D
  mon-⇒ᴿ : ∀ {J A B C D} → NL A ⊢ B → NL J ⋯ C ⊢ D → NL J ⋯ B ⇒ C ⊢ A ⇒ D
  mon-⇐ᴸ : ∀ {J A B C D} → NL J ⋯ A ⊢ B → NL C ⊢ D → NL J ⋯ A ⇐ D ⊢ B ⇐ C
  mon-⇐ᴿ : ∀ {J A B C D} → NL A ⊢ B → NL J ⋯ C ⊢ D → NL J ⋯ A ⇐ D ⊢ B ⇐ C
  res-⇒⊗ : ∀ {J A B C}   → NL J ⋯ B ⊢ A ⇒ C → NL J ⋯ A ⊗ B ⊢ C
  res-⊗⇒ : ∀ {J A B C}   → NL J ⋯ A ⊗ B ⊢ C → NL J ⋯ B ⊢ A ⇒ C
  res-⇐⊗ : ∀ {J A B C}   → NL J ⋯ A ⊢ C ⇐ B → NL J ⋯ A ⊗ B ⊢ C
  res-⊗⇐ : ∀ {J A B C}   → NL J ⋯ A ⊗ B ⊢ C → NL J ⋯ A ⊢ C ⇐ B


infix 5 is-[]_ is-[]?_

-- We can also define the property of being empty for a proof context;
-- the reason we do this is because we cannot directly use decidable
-- equality due to the fact that [] forces the types of A and C and B
-- and D to be equal.
data is-[]_ : {I J : Judgement} (f : NL I ⋯ J) → Set ℓ where
  [] : ∀ {I} → is-[] ([] {I})


is-[]?_ : ∀ {I J} (f : NL I ⋯ J) → Dec (is-[] f)
is-[]? []         = yes []
is-[]? mon-⊗ᴸ _ _ = no (λ ())
is-[]? mon-⊗ᴿ _ _ = no (λ ())
is-[]? mon-⇒ᴸ _ _ = no (λ ())
is-[]? mon-⇒ᴿ _ _ = no (λ ())
is-[]? mon-⇐ᴸ _ _ = no (λ ())
is-[]? mon-⇐ᴿ _ _ = no (λ ())
is-[]? res-⇒⊗ _   = no (λ ())
is-[]? res-⊗⇒ _   = no (λ ())
is-[]? res-⇐⊗ _   = no (λ ())
is-[]? res-⊗⇐ _   = no (λ ())


private
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
  <>-def : ∀ {I J K} (g : NL J ⋯ K) (f : NL I ⋯ J) (h : NL I)
         → (g < f >) [ h ] ≡ g [ f [ h ] ]
  <>-def []             f h = refl
  <>-def (res-⇒⊗ g)     f h rewrite <>-def g  f h = refl
  <>-def (res-⊗⇒ g)     f h rewrite <>-def g  f h = refl
  <>-def (res-⇐⊗ g)     f h rewrite <>-def g  f h = refl
  <>-def (res-⊗⇐ g)     f h rewrite <>-def g  f h = refl
  <>-def (mon-⊗ᴸ g₁ g₂) f h rewrite <>-def g₁ f h = refl
  <>-def (mon-⊗ᴿ g₁ g₂) f h rewrite <>-def g₂ f h = refl
  <>-def (mon-⇒ᴸ g₁ g₂) f h rewrite <>-def g₁ f h = refl
  <>-def (mon-⇒ᴿ g₁ g₂) f h rewrite <>-def g₂ f h = refl
  <>-def (mon-⇐ᴸ g₁ g₂) f h rewrite <>-def g₁ f h = refl
  <>-def (mon-⇐ᴿ g₁ g₂) f h rewrite <>-def g₂ f h = refl

  <>-assoc : ∀ {A B C D} (x : NL C ⋯ D) (y : NL B ⋯ C) (z : NL A ⋯ B)
           → (x < y >) < z > ≡ x < y < z > >
  <>-assoc []             y z = refl
  <>-assoc (mon-⊗ᴸ x₁ x₂) y z rewrite <>-assoc x₁ y z = refl
  <>-assoc (mon-⊗ᴿ x₁ x₂) y z rewrite <>-assoc x₂ y z = refl
  <>-assoc (mon-⇒ᴸ x₁ x₂) y z rewrite <>-assoc x₁ y z = refl
  <>-assoc (mon-⇒ᴿ x₁ x₂) y z rewrite <>-assoc x₂ y z = refl
  <>-assoc (mon-⇐ᴸ x₁ x₂) y z rewrite <>-assoc x₁ y z = refl
  <>-assoc (mon-⇐ᴿ x₁ x₂) y z rewrite <>-assoc x₂ y z = refl
  <>-assoc (res-⇒⊗ x)     y z rewrite <>-assoc x  y z = refl
  <>-assoc (res-⊗⇒ x)     y z rewrite <>-assoc x  y z = refl
  <>-assoc (res-⇐⊗ x)     y z rewrite <>-assoc x  y z = refl
  <>-assoc (res-⊗⇐ x)     y z rewrite <>-assoc x  y z = refl

  <>-identityˡ : ∀ {A B} (x : NL A ⋯ B) → [] < x > ≡ x
  <>-identityˡ _ = refl

  <>-identityʳ : ∀ {A B} (x : NL A ⋯ B) → x < [] > ≡ x
  <>-identityʳ []             = refl
  <>-identityʳ (mon-⊗ᴸ x₁ x₂) rewrite <>-identityʳ x₁ = refl
  <>-identityʳ (mon-⊗ᴿ x₁ x₂) rewrite <>-identityʳ x₂ = refl
  <>-identityʳ (mon-⇒ᴸ x₁ x₂) rewrite <>-identityʳ x₁ = refl
  <>-identityʳ (mon-⇒ᴿ x₁ x₂) rewrite <>-identityʳ x₂ = refl
  <>-identityʳ (mon-⇐ᴸ x₁ x₂) rewrite <>-identityʳ x₁ = refl
  <>-identityʳ (mon-⇐ᴿ x₁ x₂) rewrite <>-identityʳ x₂ = refl
  <>-identityʳ (res-⇒⊗ x)     rewrite <>-identityʳ x  = refl
  <>-identityʳ (res-⊗⇒ x)     rewrite <>-identityʳ x  = refl
  <>-identityʳ (res-⇐⊗ x)     rewrite <>-identityʳ x  = refl
  <>-identityʳ (res-⊗⇐ x)     rewrite <>-identityʳ x  = refl

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

instance
  functor : Functor category (set→category ℓ)
  functor = record
    { F₀           = NL_
    ; F₁           = _[_]
    ; identity     = refl
    ; homomorphism = λ {_} {_} {_} {f} {g} → <>-def g f _
    ; F-resp-≈     = F-resp-≈
    }
    where
      F-resp-≈ : ∀ {I J} {f g : NL I ⋯ J} → f ≡ g → ∀ {x} → f [ x ] ≡ g [ x ]
      F-resp-≈ refl = refl
