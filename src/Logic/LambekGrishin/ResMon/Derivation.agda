------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Category using (Category; Functor; Sets)
open import Function using (_∘_)
open import Data.Product using (∃; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.LambekGrishin.ResMon.Derivation {ℓ} (Univ : Set ℓ) where


open import Logic.LambekGrishin.Type Univ
open import Logic.LambekGrishin.ResMon.Base Univ
open import Logic.Judgement Type Type


infix 3 LG_⋯_


data LG_⋯_ : (I J : Judgement) → Set ℓ where
  []     : ∀ {J}         → LG J ⋯ J

  -- rules for residuation and monotonicity
  res-⇒⊗ : ∀ {J A B C}   → LG J ⋯ B ⊢ A ⇒ C → LG J ⋯ A ⊗ B ⊢ C
  res-⊗⇒ : ∀ {J A B C}   → LG J ⋯ A ⊗ B ⊢ C → LG J ⋯ B ⊢ A ⇒ C
  res-⇐⊗ : ∀ {J A B C}   → LG J ⋯ A ⊢ C ⇐ B → LG J ⋯ A ⊗ B ⊢ C
  res-⊗⇐ : ∀ {J A B C}   → LG J ⋯ A ⊗ B ⊢ C → LG J ⋯ A ⊢ C ⇐ B
  mon-⊗ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⊗ C ⊢ B ⊗ D
  mon-⊗ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⊗ C ⊢ B ⊗ D
  mon-⇒ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ B ⇒ C ⊢ A ⇒ D
  mon-⇒ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ B ⇒ C ⊢ A ⇒ D
  mon-⇐ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⇐ D ⊢ B ⇐ C
  mon-⇐ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⇐ D ⊢ B ⇐ C

  -- rules for co-residuation and co-monotonicity
  res-⇛⊕ : ∀ {J A B C}   → LG J ⋯ B ⇛ C ⊢ A → LG J ⋯ C ⊢ B ⊕ A
  res-⊕⇛ : ∀ {J A B C}   → LG J ⋯ C ⊢ B ⊕ A → LG J ⋯ B ⇛ C ⊢ A
  res-⊕⇚ : ∀ {J A B C}   → LG J ⋯ C ⊢ B ⊕ A → LG J ⋯ C ⇚ A ⊢ B
  res-⇚⊕ : ∀ {J A B C}   → LG J ⋯ C ⇚ A ⊢ B → LG J ⋯ C ⊢ B ⊕ A
  mon-⊕ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⊕ C ⊢ B ⊕ D
  mon-⊕ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⊕ C ⊢ B ⊕ D
  mon-⇛ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ D ⇛ A ⊢ C ⇛ B
  mon-⇛ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ D ⇛ A ⊢ C ⇛ B
  mon-⇚ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⇚ D ⊢ B ⇚ C
  mon-⇚ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⇚ D ⊢ B ⇚ C

  -- grishin distributives
  grish₁ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ C ⇛ A ⊢ D ⇐ B
  grish₂ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ C ⇛ B ⊢ A ⇒ D
  grish₃ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ B ⇚ D ⊢ A ⇒ C
  grish₄ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ A ⇚ D ⊢ C ⇐ B


-- We can also define the property of being empty for a proof context;
-- the reason we do this is because we cannot directly use decidable
-- equality due to the fact that [] forces the types of A and C and B
-- and D to be equal.

infix 5 is-[]_ is-[]?_

data is-[]_ : {I J : Judgement} (f : LG I ⋯ J) → Set ℓ where
  [] : ∀ {I} → is-[] ([] {I})

is-[]?_ : ∀ {I J} (f : LG I ⋯ J) → Dec (is-[] f)
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
is-[]? res-⇛⊕ _   = no (λ ())
is-[]? res-⊕⇛ _   = no (λ ())
is-[]? res-⊕⇚ _   = no (λ ())
is-[]? res-⇚⊕ _   = no (λ ())
is-[]? mon-⊕ᴸ _ _ = no (λ ())
is-[]? mon-⊕ᴿ _ _ = no (λ ())
is-[]? mon-⇛ᴸ _ _ = no (λ ())
is-[]? mon-⇛ᴿ _ _ = no (λ ())
is-[]? mon-⇚ᴸ _ _ = no (λ ())
is-[]? mon-⇚ᴿ _ _ = no (λ ())
is-[]? grish₁ _   = no (λ ())
is-[]? grish₂ _   = no (λ ())
is-[]? grish₃ _   = no (λ ())
is-[]? grish₄ _   = no (λ ())


module Simple where


  -- Proof contexts can be applied, by inserting the proof into the hole
  -- in the proof context.
  _[_] : ∀ {I J} → LG I ⋯ J → LG I → LG J
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
  res-⇛⊕ f     [ g ] = res-⇛⊕ (f  [ g ])
  res-⊕⇛ f     [ g ] = res-⊕⇛ (f  [ g ])
  res-⊕⇚ f     [ g ] = res-⊕⇚ (f  [ g ])
  res-⇚⊕ f     [ g ] = res-⇚⊕ (f  [ g ])
  mon-⊕ᴸ f₁ f₂ [ g ] = mon-⊕  (f₁ [ g ])  f₂
  mon-⊕ᴿ f₁ f₂ [ g ] = mon-⊕   f₁        (f₂ [ g ])
  mon-⇛ᴸ f₁ f₂ [ g ] = mon-⇛  (f₁ [ g ])  f₂
  mon-⇛ᴿ f₁ f₂ [ g ] = mon-⇛   f₁        (f₂ [ g ])
  mon-⇚ᴸ f₁ f₂ [ g ] = mon-⇚  (f₁ [ g ])  f₂
  mon-⇚ᴿ f₁ f₂ [ g ] = mon-⇚   f₁        (f₂ [ g ])
  grish₁ f     [ g ] = grish₁ (f  [ g ])
  grish₂ f     [ g ] = grish₂ (f  [ g ])
  grish₃ f     [ g ] = grish₃ (f  [ g ])
  grish₄ f     [ g ] = grish₄ (f  [ g ])



  -- Proof contexts can also be composed, simply by plugging the one
  -- proof context into the hole in the other proof context.
  _<_> : ∀ {I J K} (f : LG J ⋯ K) (g : LG I ⋯ J) → LG I ⋯ K
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
  res-⇛⊕ f     < g > = res-⇛⊕ (f  < g >)
  res-⊕⇛ f     < g > = res-⊕⇛ (f  < g >)
  res-⊕⇚ f     < g > = res-⊕⇚ (f  < g >)
  res-⇚⊕ f     < g > = res-⇚⊕ (f  < g >)
  mon-⊕ᴸ f₁ f₂ < g > = mon-⊕ᴸ (f₁ < g >)  f₂
  mon-⊕ᴿ f₁ f₂ < g > = mon-⊕ᴿ  f₁        (f₂ < g >)
  mon-⇛ᴸ f₁ f₂ < g > = mon-⇛ᴸ (f₁ < g >)  f₂
  mon-⇛ᴿ f₁ f₂ < g > = mon-⇛ᴿ  f₁        (f₂ < g >)
  mon-⇚ᴸ f₁ f₂ < g > = mon-⇚ᴸ (f₁ < g >)  f₂
  mon-⇚ᴿ f₁ f₂ < g > = mon-⇚ᴿ  f₁        (f₂ < g >)
  grish₁ f     < g > = grish₁ (f  < g >)
  grish₂ f     < g > = grish₂ (f  < g >)
  grish₃ f     < g > = grish₃ (f  < g >)
  grish₄ f     < g > = grish₄ (f  < g >)


  -- We can also show that proof context composition distributes over
  -- proof context application.
  <>-def : ∀ {I J K} (f : LG J ⋯ K) (g : LG I ⋯ J) (h : LG I)
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
  <>-def (res-⇛⊕ f)     g h rewrite <>-def f  g h = refl
  <>-def (res-⊕⇛ f)     g h rewrite <>-def f  g h = refl
  <>-def (res-⊕⇚ f)     g h rewrite <>-def f  g h = refl
  <>-def (res-⇚⊕ f)     g h rewrite <>-def f  g h = refl
  <>-def (mon-⊕ᴸ f₁ f₂) g h rewrite <>-def f₁ g h = refl
  <>-def (mon-⊕ᴿ f₁ f₂) g h rewrite <>-def f₂ g h = refl
  <>-def (mon-⇛ᴸ f₁ f₂) g h rewrite <>-def f₁ g h = refl
  <>-def (mon-⇛ᴿ f₁ f₂) g h rewrite <>-def f₂ g h = refl
  <>-def (mon-⇚ᴸ f₁ f₂) g h rewrite <>-def f₁ g h = refl
  <>-def (mon-⇚ᴿ f₁ f₂) g h rewrite <>-def f₂ g h = refl
  <>-def (grish₁ f)     g h rewrite <>-def f  g h = refl
  <>-def (grish₂ f)     g h rewrite <>-def f  g h = refl
  <>-def (grish₃ f)     g h rewrite <>-def f  g h = refl
  <>-def (grish₄ f)     g h rewrite <>-def f  g h = refl

  <>-assoc : ∀ {A B C D} (f : LG C ⋯ D) (g : LG B ⋯ C) (h : LG A ⋯ B)
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
  <>-assoc (res-⇛⊕ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (res-⊕⇛ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (res-⊕⇚ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (res-⇚⊕ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (mon-⊕ᴸ f₁ f₂) g h rewrite <>-assoc f₁ g h = refl
  <>-assoc (mon-⊕ᴿ f₁ f₂) g h rewrite <>-assoc f₂ g h = refl
  <>-assoc (mon-⇛ᴸ f₁ f₂) g h rewrite <>-assoc f₁ g h = refl
  <>-assoc (mon-⇛ᴿ f₁ f₂) g h rewrite <>-assoc f₂ g h = refl
  <>-assoc (mon-⇚ᴸ f₁ f₂) g h rewrite <>-assoc f₁ g h = refl
  <>-assoc (mon-⇚ᴿ f₁ f₂) g h rewrite <>-assoc f₂ g h = refl
  <>-assoc (grish₁ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (grish₂ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (grish₃ f)     g h rewrite <>-assoc f  g h = refl
  <>-assoc (grish₄ f)     g h rewrite <>-assoc f  g h = refl

  <>-identityˡ : ∀ {A B} (f : LG A ⋯ B) → [] < f > ≡ f
  <>-identityˡ _ = refl

  <>-identityʳ : ∀ {A B} (f : LG A ⋯ B) → f < [] > ≡ f
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
  <>-identityʳ (res-⇛⊕ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (res-⊕⇛ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (res-⊕⇚ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (res-⇚⊕ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (mon-⊕ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (mon-⊕ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (mon-⇛ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (mon-⇛ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (mon-⇚ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (mon-⇚ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (grish₁ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (grish₂ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (grish₃ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (grish₄ f)     rewrite <>-identityʳ f  = refl

  <>-resp-≡ : ∀ {A B C} {x y : LG B ⋯ C} {z w : LG A ⋯ B}
            → x ≡ y → z ≡ w → x < z > ≡ y < w >
  <>-resp-≡ p₁ p₂ rewrite p₁ | p₂ = refl


-- Proof that derivations form a category
instance
  category : Category _ _ _
  category = record
    { Obj           = Judgement
    ; Hom           = LG_⋯_
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
    { F₀           = LG_
    ; F₁           = _[_]
    ; identity     = refl
    ; homomorphism = λ {_} {_} {_} {f} {g} → <>-def g f _
    ; F-resp-≈     = F-resp-≈
    }
    where
      open Simple
      F-resp-≈ : ∀ {I J} {f g : LG I ⋯ J} → f ≡ g → ∀ {x} → f [ x ] ≡ g [ x ]
      F-resp-≈ refl = refl
