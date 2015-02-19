------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Empty                                 using (⊥-elim)
open import Data.List                                  using (List; any)
open import Data.Product                               using (Σ-syntax; _,_)
open import Data.Sum                                   using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (False; toWitnessFalse)
open import Relation.Binary                            using (module DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_; refl)


module Logic.Classical.Ordered.LambekGrishin.Decidable {ℓ} (Univ : Set ℓ) (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)) where


open import Logic.Classical.Ordered.LambekGrishin.Type       Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Judgement  Univ as J
open import Logic.Classical.Ordered.LambekGrishin.Base       Univ as B
open import Logic.Classical.Ordered.LambekGrishin.Derivation Univ as D

open J.DecEq _≟-Univ_
open DecSetoid decSetoid using (_≟_)


infix 1 _⇄_ _⇆_


data _⇄_ : (I J : Judgement) → Set ℓ where

  []     : ∀ {I} → I ⇄ I
  res-⇒⊗ : ∀ {I A B C} (f : I ⇄ B ⊢ A ⇒ C) → I ⇄ A ⊗ B ⊢ C
  res-⇐⊗ : ∀ {I A B C} (f : I ⇄ A ⊢ C ⇐ B) → I ⇄ A ⊗ B ⊢ C
  res-⊕⇛ : ∀ {I A B C} (f : I ⇄ C ⊢ B ⊕ A) → I ⇄ B ⇛ C ⊢ A
  res-⊕⇚ : ∀ {I A B C} (f : I ⇄ C ⊢ B ⊕ A) → I ⇄ C ⇚ A ⊢ B
  res-⊗⇒ : ∀ {I A B C} (f : I ⇄ A ⊗ B ⊢ C) → I ⇄ B ⊢ A ⇒ C
  res-⊗⇐ : ∀ {I A B C} (f : I ⇄ A ⊗ B ⊢ C) → I ⇄ A ⊢ C ⇐ B
  res-⇛⊕ : ∀ {I A B C} (f : I ⇄ B ⇛ C ⊢ A) → I ⇄ C ⊢ B ⊕ A
  res-⇚⊕ : ∀ {I A B C} (f : I ⇄ C ⇚ A ⊢ B) → I ⇄ C ⊢ B ⊕ A

data _⇆_ : (I J : Judgement) → Set ℓ where

  []     : ∀ {J} → J ⇆ J
  res-⊗⇒ : ∀ {J A B C} (f : B ⊢ A ⇒ C ⇆ J) → A ⊗ B ⊢ C ⇆ J
  res-⊗⇐ : ∀ {J A B C} (f : A ⊢ C ⇐ B ⇆ J) → A ⊗ B ⊢ C ⇆ J
  res-⇛⊕ : ∀ {J A B C} (f : C ⊢ B ⊕ A ⇆ J) → B ⇛ C ⊢ A ⇆ J
  res-⇚⊕ : ∀ {J A B C} (f : C ⊢ B ⊕ A ⇆ J) → C ⇚ A ⊢ B ⇆ J
  res-⇒⊗ : ∀ {J A B C} (f : A ⊗ B ⊢ C ⇆ J) → B ⊢ A ⇒ C ⇆ J
  res-⇐⊗ : ∀ {J A B C} (f : A ⊗ B ⊢ C ⇆ J) → A ⊢ C ⇐ B ⇆ J
  res-⊕⇛ : ∀ {J A B C} (f : B ⇛ C ⊢ A ⇆ J) → C ⊢ B ⊕ A ⇆ J
  res-⊕⇚ : ∀ {J A B C} (f : C ⇚ A ⊢ B ⇆ J) → C ⊢ B ⊕ A ⇆ J


-- TODO: express "all possible permutations"


⇄-sym : ∀ {I J} → I ⇄ J → J ⇆ I
⇄-sym []         = []
⇄-sym (res-⇒⊗ f) = res-⊗⇒ (⇄-sym f)
⇄-sym (res-⇐⊗ f) = res-⊗⇐ (⇄-sym f)
⇄-sym (res-⊕⇛ f) = res-⇛⊕ (⇄-sym f)
⇄-sym (res-⊕⇚ f) = res-⇚⊕ (⇄-sym f)
⇄-sym (res-⊗⇒ f) = res-⇒⊗ (⇄-sym f)
⇄-sym (res-⊗⇐ f) = res-⇐⊗ (⇄-sym f)
⇄-sym (res-⇛⊕ f) = res-⊕⇛ (⇄-sym f)
⇄-sym (res-⇚⊕ f) = res-⊕⇚ (⇄-sym f)


⇆-sym : ∀ {I J} → I ⇆ J → J ⇄ I
⇆-sym []         = []
⇆-sym (res-⇒⊗ f) = res-⊗⇒ (⇆-sym f)
⇆-sym (res-⇐⊗ f) = res-⊗⇐ (⇆-sym f)
⇆-sym (res-⊕⇛ f) = res-⇛⊕ (⇆-sym f)
⇆-sym (res-⊕⇚ f) = res-⇚⊕ (⇆-sym f)
⇆-sym (res-⊗⇒ f) = res-⇒⊗ (⇆-sym f)
⇆-sym (res-⊗⇐ f) = res-⇐⊗ (⇆-sym f)
⇆-sym (res-⇛⊕ f) = res-⊕⇛ (⇆-sym f)
⇆-sym (res-⇚⊕ f) = res-⊕⇚ (⇆-sym f)


⇄-to-→ : ∀ {I J} → I ⇄ J → LG I → LG J
⇄-to-→ []         x = x
⇄-to-→ (res-⇒⊗ f) x = res-⇒⊗ (⇄-to-→ f x)
⇄-to-→ (res-⇐⊗ f) x = res-⇐⊗ (⇄-to-→ f x)
⇄-to-→ (res-⊕⇛ f) x = res-⊕⇛ (⇄-to-→ f x)
⇄-to-→ (res-⊕⇚ f) x = res-⊕⇚ (⇄-to-→ f x)
⇄-to-→ (res-⊗⇒ f) x = res-⊗⇒ (⇄-to-→ f x)
⇄-to-→ (res-⊗⇐ f) x = res-⊗⇐ (⇄-to-→ f x)
⇄-to-→ (res-⇛⊕ f) x = res-⇛⊕ (⇄-to-→ f x)
⇄-to-→ (res-⇚⊕ f) x = res-⇚⊕ (⇄-to-→ f x)


⇆-to-→ : ∀ {I J} → I ⇆ J → LG I → LG J
⇆-to-→ []         x = x
⇆-to-→ (res-⊗⇒ f) (res-⇒⊗ x) = ⇆-to-→ f x
⇆-to-→ (res-⊗⇒ f)         x  = ⇆-to-→ f (res-⊗⇒ x)
⇆-to-→ (res-⊗⇐ f) (res-⇐⊗ x) = ⇆-to-→ f x
⇆-to-→ (res-⊗⇐ f)         x  = ⇆-to-→ f (res-⊗⇐ x)
⇆-to-→ (res-⇛⊕ f) (res-⊕⇛ x) = ⇆-to-→ f x
⇆-to-→ (res-⇛⊕ f)         x  = ⇆-to-→ f (res-⇛⊕ x)
⇆-to-→ (res-⇚⊕ f) (res-⊕⇚ x) = ⇆-to-→ f x
⇆-to-→ (res-⇚⊕ f)         x  = ⇆-to-→ f (res-⇚⊕ x)
⇆-to-→ (res-⇒⊗ f) (res-⊗⇒ x) = ⇆-to-→ f x
⇆-to-→ (res-⇒⊗ f)         x  = ⇆-to-→ f (res-⇒⊗ x)
⇆-to-→ (res-⇐⊗ f) (res-⊗⇐ x) = ⇆-to-→ f x
⇆-to-→ (res-⇐⊗ f)         x  = ⇆-to-→ f (res-⇐⊗ x)
⇆-to-→ (res-⊕⇛ f) (res-⇛⊕ x) = ⇆-to-→ f x
⇆-to-→ (res-⊕⇛ f)         x  = ⇆-to-→ f (res-⊕⇛ x)
⇆-to-→ (res-⊕⇚ f) (res-⇚⊕ x) = ⇆-to-→ f x
⇆-to-→ (res-⊕⇚ f)         x  = ⇆-to-→ f (res-⊕⇚ x)


⇄-sym-correct : ∀ {I J} (f : I ⇄ J) (x : LG I)
              → x ≡ ⇆-to-→ (⇄-sym f) (⇄-to-→ f x)
⇄-sym-correct []         x = refl
⇄-sym-correct (res-⇒⊗ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⇐⊗ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⊕⇛ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⊕⇚ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⊗⇒ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⊗⇐ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⇛⊕ f) x = ⇄-sym-correct f x
⇄-sym-correct (res-⇚⊕ f) x = ⇄-sym-correct f x


⇆-sym-correct : ∀ {I J} (f : J ⇆ I) (x : LG I)
              → x ≡ ⇆-to-→ f (⇄-to-→ (⇆-sym f) x)
⇆-sym-correct []         x = refl
⇆-sym-correct (res-⊗⇒ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⊗⇐ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⇛⊕ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⇚⊕ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⇒⊗ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⇐⊗ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⊕⇛ f) x = ⇆-sym-correct f x
⇆-sym-correct (res-⊕⇚ f) x = ⇆-sym-correct f x
