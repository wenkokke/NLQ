------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Categories.Category                        using (Category)
open import Algebra                                    using (module Monoid; Monoid)
open import Function                                   using (id; _∘_)
open import Data.Empty                                 using (⊥)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Data.Unit                                  using (⊤; tt)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Judgement.Context {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type         Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Type.Context Univ as TC hiding (module Simple; module Context; Context)
open import Logic.Classical.Ordered.LambekGrishin.Judgement    Univ


infix 3 _<⊢_ _⊢>_

data Context : Set ℓ where
  _<⊢_ : TC.Context → Type → Context
  _⊢>_ : Type → TC.Context → Context


-- Proofs which show that constructors of judgement contexts (as all
-- Agda data-constructors) respect equality.

<⊢-injective : ∀ {I J K L} → (I <⊢ J) ≡ (K <⊢ L) → I ≡ K × J ≡ L
<⊢-injective refl = refl , refl

⊢>-injective : ∀ {I J K L} → (I ⊢> J) ≡ (K ⊢> L) → I ≡ K × J ≡ L
⊢>-injective refl = refl , refl


module Simple where

  open TC.Simple renaming (_[_] to _[_]′; _<_> to _<_>′)

  -- Apply a context to a type by plugging the type into the context.
  _[_] : Context → Type → Judgement
  (A <⊢ B) [ C ] = A [ C ]′ ⊢ B
  (A ⊢> B) [ C ] = A ⊢ B [ C ]′

  -- Insert a context into a judgement context
  _<_> : Context → TC.Context → Context
  _<_> (A <⊢ B) C = A < C >′ <⊢ B
  _<_> (A ⊢> B) C = A ⊢> B < C >′