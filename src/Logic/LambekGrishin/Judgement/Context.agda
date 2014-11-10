------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Categories
open import Level using (zero)
open import Algebra using (module Monoid; Monoid)
open import Function using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Data.Unit as Unit using (⊤; tt)


module Logic.LambekGrishin.Judgement.Context {ℓ} (Univ : Set ℓ) where

open import Logic.LambekGrishin.Type         Univ as T
open import Logic.LambekGrishin.Type.Context Univ as TC hiding (module Simple)
open import Logic.LambekGrishin.Judgement    Univ as J


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


module Simple where

  open TC.Simple renaming (_[_] to _[_]′; _<_> to _<_>′)

  -- Apply a context to a type by plugging the type into the context.
  _[_] : JudgementContext → Type → Judgement
  (A <⊢ B) [ C ] = A [ C ]′ ⊢ B
  (A ⊢> B) [ C ] = A ⊢ B [ C ]′

  -- Insert a context into a judgement context
  _<_> : JudgementContext → Context → JudgementContext
  _<_> (A <⊢ B) C = A < C >′ <⊢ B
  _<_> (A ⊢> B) C = A ⊢> B < C >′
