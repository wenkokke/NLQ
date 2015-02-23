------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements derivations---also known as partial proofs or term
-- contexts---which are generally written as:
--
--     A ⊢ B
--     -----
--       ⋮
--     -----
--     C ⊢ D
--
-- This definition guarantees that there is exactly *one* sub-proof
-- missing. In addition, this module provides proofs that these
-- contexts form a category, and thus behave function-like.
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Categories.Category                        using (Category)
open import Categories.Functor                         using (Functor)
open import Categories.Agda                            using (Sets)
open import Data.Empty                                 using (⊥)
open import Data.Product                               using (∃; _,_)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.ResMon.Derivation {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type             Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Univ


infix 1 LG_⋯_


data LG_⋯_ : (I J : Judgement) → Set ℓ where
  []     : ∀ {J}         → LG J ⋯ J


  -- rules for unary residuation and monotonicity
  m□  : ∀ {J A B}     → LG J ⋯   A ⊢   B → LG J ⋯ □ A ⊢ □ B
  m◇  : ∀ {J A B}     → LG J ⋯   A ⊢   B → LG J ⋯ ◇ A ⊢ ◇ B
  r□◇ : ∀ {J A B}     → LG J ⋯   A ⊢ □ B → LG J ⋯ ◇ A ⊢   B
  r◇□ : ∀ {J A B}     → LG J ⋯ ◇ A ⊢   B → LG J ⋯   A ⊢ □ B

  -- rules for residuation and monotonicity
  r⇒⊗ : ∀ {J A B C}   → LG J ⋯ B ⊢ A ⇒ C → LG J ⋯ A ⊗ B ⊢ C
  r⊗⇒ : ∀ {J A B C}   → LG J ⋯ A ⊗ B ⊢ C → LG J ⋯ B ⊢ A ⇒ C
  r⇐⊗ : ∀ {J A B C}   → LG J ⋯ A ⊢ C ⇐ B → LG J ⋯ A ⊗ B ⊢ C
  r⊗⇐ : ∀ {J A B C}   → LG J ⋯ A ⊗ B ⊢ C → LG J ⋯ A ⊢ C ⇐ B
  m⊗ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⊗ C ⊢ B ⊗ D
  m⊗ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⊗ C ⊢ B ⊗ D
  m⇒ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ B ⇒ C ⊢ A ⇒ D
  m⇒ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ B ⇒ C ⊢ A ⇒ D
  m⇐ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⇐ D ⊢ B ⇐ C
  m⇐ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⇐ D ⊢ B ⇐ C

  -- rules for co-residuation and co-monotonicity
  r⇛⊕ : ∀ {J A B C}   → LG J ⋯ B ⇛ C ⊢ A → LG J ⋯ C ⊢ B ⊕ A
  r⊕⇛ : ∀ {J A B C}   → LG J ⋯ C ⊢ B ⊕ A → LG J ⋯ B ⇛ C ⊢ A
  r⊕⇚ : ∀ {J A B C}   → LG J ⋯ C ⊢ B ⊕ A → LG J ⋯ C ⇚ A ⊢ B
  r⇚⊕ : ∀ {J A B C}   → LG J ⋯ C ⇚ A ⊢ B → LG J ⋯ C ⊢ B ⊕ A
  m⊕ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⊕ C ⊢ B ⊕ D
  m⊕ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⊕ C ⊢ B ⊕ D
  m⇛ᴸ : ∀ {J A B C D} → LG J ⋯ C ⊢ D → LG A ⊢ B → LG J ⋯ D ⇛ A ⊢ C ⇛ B
  m⇛ᴿ : ∀ {J A B C D} → LG C ⊢ D → LG J ⋯ A ⊢ B → LG J ⋯ D ⇛ A ⊢ C ⇛ B
  m⇚ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⇚ D ⊢ B ⇚ C
  m⇚ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⇚ D ⊢ B ⇚ C

  -- grishin distributives
  d⇛⇐ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ C ⇛ A ⊢ D ⇐ B
  d⇛⇒ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ C ⇛ B ⊢ A ⇒ D
  d⇚⇒ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ B ⇚ D ⊢ A ⇒ C
  d⇚⇐ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ A ⇚ D ⊢ C ⇐ B


-- We can also define the property of being empty for a proof context;
-- the reason we do this is because we cannot directly use decidable
-- equality due to the fact that [] forces the types of A and C and B
-- and D to be equal.

infix 5 is-[]_ is-[]?_

data is-[]_ : {I J : Judgement} (f : LG I ⋯ J) → Set ℓ where
  [] : ∀ {I} → is-[] ([] {I})

is-[]?_ : ∀ {I J} (f : LG I ⋯ J) → Dec (is-[] f)
is-[]? []         = yes []
is-[]? m□  _   = no (λ ())
is-[]? m◇  _   = no (λ ())
is-[]? r□◇ _   = no (λ ())
is-[]? r◇□ _   = no (λ ())
is-[]? r⇒⊗ _   = no (λ ())
is-[]? r⊗⇒ _   = no (λ ())
is-[]? r⇐⊗ _   = no (λ ())
is-[]? r⊗⇐ _   = no (λ ())
is-[]? m⊗ᴸ _ _ = no (λ ())
is-[]? m⊗ᴿ _ _ = no (λ ())
is-[]? m⇒ᴸ _ _ = no (λ ())
is-[]? m⇒ᴿ _ _ = no (λ ())
is-[]? m⇐ᴸ _ _ = no (λ ())
is-[]? m⇐ᴿ _ _ = no (λ ())
is-[]? r⇛⊕ _   = no (λ ())
is-[]? r⊕⇛ _   = no (λ ())
is-[]? r⊕⇚ _   = no (λ ())
is-[]? r⇚⊕ _   = no (λ ())
is-[]? m⊕ᴸ _ _ = no (λ ())
is-[]? m⊕ᴿ _ _ = no (λ ())
is-[]? m⇛ᴸ _ _ = no (λ ())
is-[]? m⇛ᴿ _ _ = no (λ ())
is-[]? m⇚ᴸ _ _ = no (λ ())
is-[]? m⇚ᴿ _ _ = no (λ ())
is-[]? d⇛⇐ _   = no (λ ())
is-[]? d⇛⇒ _   = no (λ ())
is-[]? d⇚⇒ _   = no (λ ())
is-[]? d⇚⇐ _   = no (λ ())


module Simple where


  -- Proof contexts can be applied, by inserting the proof into the hole
  -- in the proof context.
  _[_] : ∀ {I J} → LG I ⋯ J → LG I → LG J
  []           [ g ] = g
  m□  f     [ g ] = m□  (f  [ g ])
  m◇  f     [ g ] = m◇  (f  [ g ])
  r□◇ f     [ g ] = r□◇ (f  [ g ])
  r◇□ f     [ g ] = r◇□ (f  [ g ])
  r⇒⊗ f     [ g ] = r⇒⊗ (f  [ g ])
  r⊗⇒ f     [ g ] = r⊗⇒ (f  [ g ])
  r⇐⊗ f     [ g ] = r⇐⊗ (f  [ g ])
  r⊗⇐ f     [ g ] = r⊗⇐ (f  [ g ])
  m⊗ᴸ f₁ f₂ [ g ] = m⊗  (f₁ [ g ])  f₂
  m⊗ᴿ f₁ f₂ [ g ] = m⊗   f₁        (f₂ [ g ])
  m⇒ᴸ f₁ f₂ [ g ] = m⇒  (f₁ [ g ])  f₂
  m⇒ᴿ f₁ f₂ [ g ] = m⇒   f₁        (f₂ [ g ])
  m⇐ᴸ f₁ f₂ [ g ] = m⇐  (f₁ [ g ])  f₂
  m⇐ᴿ f₁ f₂ [ g ] = m⇐   f₁        (f₂ [ g ])
  r⇛⊕ f     [ g ] = r⇛⊕ (f  [ g ])
  r⊕⇛ f     [ g ] = r⊕⇛ (f  [ g ])
  r⊕⇚ f     [ g ] = r⊕⇚ (f  [ g ])
  r⇚⊕ f     [ g ] = r⇚⊕ (f  [ g ])
  m⊕ᴸ f₁ f₂ [ g ] = m⊕  (f₁ [ g ])  f₂
  m⊕ᴿ f₁ f₂ [ g ] = m⊕   f₁        (f₂ [ g ])
  m⇛ᴸ f₁ f₂ [ g ] = m⇛  (f₁ [ g ])  f₂
  m⇛ᴿ f₁ f₂ [ g ] = m⇛   f₁        (f₂ [ g ])
  m⇚ᴸ f₁ f₂ [ g ] = m⇚  (f₁ [ g ])  f₂
  m⇚ᴿ f₁ f₂ [ g ] = m⇚   f₁        (f₂ [ g ])
  d⇛⇐ f     [ g ] = d⇛⇐ (f  [ g ])
  d⇛⇒ f     [ g ] = d⇛⇒ (f  [ g ])
  d⇚⇒ f     [ g ] = d⇚⇒ (f  [ g ])
  d⇚⇐ f     [ g ] = d⇚⇐ (f  [ g ])



  -- Proof contexts can also be composed, simply by plugging the one
  -- proof context into the hole in the other proof context.
  _<_> : ∀ {I J K} (f : LG J ⋯ K) (g : LG I ⋯ J) → LG I ⋯ K
  []           < g > = g
  m□  f     < g > = m□  (f  < g >)
  m◇  f     < g > = m◇  (f  < g >)
  r□◇ f     < g > = r□◇ (f  < g >)
  r◇□ f     < g > = r◇□ (f  < g >)
  r⇒⊗ f     < g > = r⇒⊗ (f  < g >)
  r⊗⇒ f     < g > = r⊗⇒ (f  < g >)
  r⇐⊗ f     < g > = r⇐⊗ (f  < g >)
  r⊗⇐ f     < g > = r⊗⇐ (f  < g >)
  m⊗ᴸ f₁ f₂ < g > = m⊗ᴸ (f₁ < g >)  f₂
  m⊗ᴿ f₁ f₂ < g > = m⊗ᴿ  f₁        (f₂ < g >)
  m⇒ᴸ f₁ f₂ < g > = m⇒ᴸ (f₁ < g >)  f₂
  m⇒ᴿ f₁ f₂ < g > = m⇒ᴿ  f₁        (f₂ < g >)
  m⇐ᴸ f₁ f₂ < g > = m⇐ᴸ (f₁ < g >)  f₂
  m⇐ᴿ f₁ f₂ < g > = m⇐ᴿ  f₁        (f₂ < g >)
  r⇛⊕ f     < g > = r⇛⊕ (f  < g >)
  r⊕⇛ f     < g > = r⊕⇛ (f  < g >)
  r⊕⇚ f     < g > = r⊕⇚ (f  < g >)
  r⇚⊕ f     < g > = r⇚⊕ (f  < g >)
  m⊕ᴸ f₁ f₂ < g > = m⊕ᴸ (f₁ < g >)  f₂
  m⊕ᴿ f₁ f₂ < g > = m⊕ᴿ  f₁        (f₂ < g >)
  m⇛ᴸ f₁ f₂ < g > = m⇛ᴸ (f₁ < g >)  f₂
  m⇛ᴿ f₁ f₂ < g > = m⇛ᴿ  f₁        (f₂ < g >)
  m⇚ᴸ f₁ f₂ < g > = m⇚ᴸ (f₁ < g >)  f₂
  m⇚ᴿ f₁ f₂ < g > = m⇚ᴿ  f₁        (f₂ < g >)
  d⇛⇐ f     < g > = d⇛⇐ (f  < g >)
  d⇛⇒ f     < g > = d⇛⇒ (f  < g >)
  d⇚⇒ f     < g > = d⇚⇒ (f  < g >)
  d⇚⇐ f     < g > = d⇚⇐ (f  < g >)


  -- We can also show that proof context composition distributes over
  -- proof context application.
  <>-def : ∀ {I J K} (f : LG I ⋯ J) (g : LG J ⋯ K) (x : LG I)
         → (g < f >) [ x ] ≡ g [ f [ x ] ]
  <>-def f []             x = refl
  <>-def f (m□  g)     x rewrite <>-def f g  x = refl
  <>-def f (m◇  g)     x rewrite <>-def f g  x = refl
  <>-def f (r□◇ g)     x rewrite <>-def f g  x = refl
  <>-def f (r◇□ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⇒⊗ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⊗⇒ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⇐⊗ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⊗⇐ g)     x rewrite <>-def f g  x = refl
  <>-def f (m⊗ᴸ g₁ g₂) x rewrite <>-def f g₁ x = refl
  <>-def f (m⊗ᴿ g₁ g₂) x rewrite <>-def f g₂ x = refl
  <>-def f (m⇒ᴸ g₁ g₂) x rewrite <>-def f g₁ x = refl
  <>-def f (m⇒ᴿ g₁ g₂) x rewrite <>-def f g₂ x = refl
  <>-def f (m⇐ᴸ g₁ g₂) x rewrite <>-def f g₁ x = refl
  <>-def f (m⇐ᴿ g₁ g₂) x rewrite <>-def f g₂ x = refl
  <>-def f (r⇛⊕ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⊕⇛ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⊕⇚ g)     x rewrite <>-def f g  x = refl
  <>-def f (r⇚⊕ g)     x rewrite <>-def f g  x = refl
  <>-def f (m⊕ᴸ g₁ g₂) x rewrite <>-def f g₁ x = refl
  <>-def f (m⊕ᴿ g₁ g₂) x rewrite <>-def f g₂ x = refl
  <>-def f (m⇛ᴸ g₁ g₂) x rewrite <>-def f g₁ x = refl
  <>-def f (m⇛ᴿ g₁ g₂) x rewrite <>-def f g₂ x = refl
  <>-def f (m⇚ᴸ g₁ g₂) x rewrite <>-def f g₁ x = refl
  <>-def f (m⇚ᴿ g₁ g₂) x rewrite <>-def f g₂ x = refl
  <>-def f (d⇛⇐ g)     x rewrite <>-def f g  x = refl
  <>-def f (d⇛⇒ g)     x rewrite <>-def f g  x = refl
  <>-def f (d⇚⇒ g)     x rewrite <>-def f g  x = refl
  <>-def f (d⇚⇐ g)     x rewrite <>-def f g  x = refl

  <>-assoc : ∀ {A B C D} (h : LG A ⋯ B) (g : LG B ⋯ C) (f : LG C ⋯ D)
           → (f < g >) < h > ≡ f < g < h > >
  <>-assoc h g []             = refl
  <>-assoc h g (m□  f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (m◇  f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r□◇ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r◇□ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⇒⊗ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⊗⇒ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⇐⊗ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⊗⇐ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (m⊗ᴸ f₁ f₂) rewrite <>-assoc h g f₁ = refl
  <>-assoc h g (m⊗ᴿ f₁ f₂) rewrite <>-assoc h g f₂ = refl
  <>-assoc h g (m⇒ᴸ f₁ f₂) rewrite <>-assoc h g f₁ = refl
  <>-assoc h g (m⇒ᴿ f₁ f₂) rewrite <>-assoc h g f₂ = refl
  <>-assoc h g (m⇐ᴸ f₁ f₂) rewrite <>-assoc h g f₁ = refl
  <>-assoc h g (m⇐ᴿ f₁ f₂) rewrite <>-assoc h g f₂ = refl
  <>-assoc h g (r⇛⊕ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⊕⇛ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⊕⇚ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (r⇚⊕ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (m⊕ᴸ f₁ f₂) rewrite <>-assoc h g f₁ = refl
  <>-assoc h g (m⊕ᴿ f₁ f₂) rewrite <>-assoc h g f₂ = refl
  <>-assoc h g (m⇛ᴸ f₁ f₂) rewrite <>-assoc h g f₁ = refl
  <>-assoc h g (m⇛ᴿ f₁ f₂) rewrite <>-assoc h g f₂ = refl
  <>-assoc h g (m⇚ᴸ f₁ f₂) rewrite <>-assoc h g f₁ = refl
  <>-assoc h g (m⇚ᴿ f₁ f₂) rewrite <>-assoc h g f₂ = refl
  <>-assoc h g (d⇛⇐ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (d⇛⇒ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (d⇚⇒ f)     rewrite <>-assoc h g f  = refl
  <>-assoc h g (d⇚⇐ f)     rewrite <>-assoc h g f  = refl

  <>-identityˡ : ∀ {A B} (f : LG A ⋯ B) → [] < f > ≡ f
  <>-identityˡ _ = refl

  <>-identityʳ : ∀ {A B} (f : LG A ⋯ B) → f < [] > ≡ f
  <>-identityʳ []             = refl
  <>-identityʳ (m□  f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (m◇  f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r□◇ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r◇□ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (m⊗ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (m⊗ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (m⇒ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (m⇒ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (m⇐ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (m⇐ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (r⇒⊗ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⊗⇒ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⇐⊗ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⊗⇐ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⇛⊕ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⊕⇛ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⊕⇚ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (r⇚⊕ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (m⊕ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (m⊕ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (m⇛ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (m⇛ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (m⇚ᴸ f₁ f₂) rewrite <>-identityʳ f₁ = refl
  <>-identityʳ (m⇚ᴿ f₁ f₂) rewrite <>-identityʳ f₂ = refl
  <>-identityʳ (d⇛⇐ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (d⇛⇒ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (d⇚⇒ f)     rewrite <>-identityʳ f  = refl
  <>-identityʳ (d⇚⇐ f)     rewrite <>-identityʳ f  = refl

  <>-resp-≡ : ∀ {A B C} {x y : LG B ⋯ C} {z w : LG A ⋯ B}
            → x ≡ y → z ≡ w → x < z > ≡ y < w >
  <>-resp-≡ p₁ p₂ rewrite p₁ | p₂ = refl


-- Proof that derivations form a category
instance
  category : Category ℓ ℓ ℓ
  category = record
    { Obj       = Judgement
    ; _⇒_       = LG_⋯_
    ; _≡_       = _≡_
    ; id        = []
    ; _∘_       = _<_>
    ; assoc     = λ {_}{_}{_}{_}{f}{g}{h} → <>-assoc f g h
    ; identityˡ = λ {_}{_}            {f} → <>-identityˡ f
    ; identityʳ = λ {_}{_}            {f} → <>-identityʳ f
    ; ∘-resp-≡  = <>-resp-≡
    ; equiv     = P.isEquivalence
    }
    where open Simple

instance
  functor : Functor category (Sets ℓ)
  functor = record
    { F₀           = LG_
    ; F₁           = _[_]
    ; identity     = refl
    ; homomorphism = λ {_}{_}{_}{f}{g}{x} → <>-def f g x
    ; F-resp-≡     = F-resp-≡
    }
    where
      open Simple
      F-resp-≡ : ∀ {I J} {f g : LG I ⋯ J} → f ≡ g → ∀ {x} → f [ x ] ≡ g [ x ]
      F-resp-≡ refl = refl
