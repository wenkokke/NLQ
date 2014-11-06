------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Category using (Category; Functor; Monoids; Sets)
open import Algebra using (Monoid)
open import Function using (flip; _∘_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Judgement.Context.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ
open import Logic.Type.Context.Polarised Univ
     as Context hiding (module Polarised; module Simple) renaming (Polarised to Context)
open import Logic.Judgement Type Type
open import Logic.Judgement.Context Univ
     as JudgementContext hiding (module Simple)
open import Logic.Polarity


data Polarised (p : Polarity) : JudgementContext → Set ℓ where
  _<⊢_ : ∀ {A} (A⁺ : Context p + A) (B : Type) → Polarised p (A <⊢ B)
  _⊢>_ : ∀ (A : Type) {B} (B⁻ : Context p - B) → Polarised p (A ⊢> B)


module Simple where

  open Context.Simple using () renaming (_[_] to _[_]′; _<_> to _<_>″)
  open JudgementContext.Simple using () renaming (_<_> to _<_>′)

  -- Apply judgement contexts to types to get judgements
  _[_] : ∀ {p J} → Polarised p J → Type → Judgement
  (A <⊢ B) [ C ] = A [ C ]′ ⊢ B
  (A ⊢> B) [ C ] = A ⊢ B [ C ]′

  -- Insert context into judgement contexts to get judgement contexts
  _<_> : ∀ {p₁ p₂ J A} → Polarised p₂ J → Context p₁ p₂ A → Polarised p₁ (J < A >′)
  (A <⊢ B) < C > = A < C >″ <⊢ B
  (A ⊢> B) < C > = A ⊢> B < C >″
