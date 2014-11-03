------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


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
