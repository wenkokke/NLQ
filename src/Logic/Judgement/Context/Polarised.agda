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
open import Logic.Polarity


module Logic.Judgement.Context.Polarised
  {ℓ}
  (Type : Set ℓ)
  (Context : Set ℓ)
  (_[_]ᶜ : Context → Type → Type)
  (_<_>ᶜ : Context → Context → Context)
  (Polarisedᶜ : Polarity → Polarity → Context → Set ℓ)
  (_[_]ᴾ : ∀ {p₁ p₂ A} → Polarisedᶜ p₁ p₂ A → Type → Type)
  (_<_>ᴾ : ∀ {p₁ p₂ p₃ A B} → Polarisedᶜ p₂ p₃ A → Polarisedᶜ p₁ p₂ B → Polarisedᶜ p₁ p₃ (A < B >ᶜ))
  where


open import Logic.Judgement Type Type
open import Logic.Judgement.Context Type Context _[_]ᶜ _<_>ᶜ
     using (JudgementContext; _<⊢_; _⊢>_) renaming (_[_] to _[_]ᴶ; _<_> to _<_>ᴶ)


data Polarised (p : Polarity) : JudgementContext → Set ℓ where
  _<⊢_ : ∀ {A} (A⁺ : Polarisedᶜ p + A) (B : Type) → Polarised p (A <⊢ B)
  _⊢>_ : ∀ (A : Type) {B} (B⁻ : Polarisedᶜ p - B) → Polarised p (A ⊢> B)


-- Apply judgement contexts to types to get judgements
_[_] : ∀ {p J} → Polarised p J → Type → Judgement
(A <⊢ B) [ C ] = A [ C ]ᴾ ⊢ B
(A ⊢> B) [ C ] = A ⊢ B [ C ]ᴾ

-- Insert context into judgement contexts to get judgement contexts
_<_> : ∀ {p₁ p₂ J A} → Polarised p₂ J → Polarisedᶜ p₁ p₂ A → Polarised p₁ (J < A >ᴶ)
(A <⊢ B) < C > = A < C >ᴾ <⊢ B
(A ⊢> B) < C > = A ⊢> B < C >ᴾ
