------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level                                      using (zero)
open import Algebra                                    using (Monoid)
open import Function                                   using (id; flip; _∘_)
open import Data.Empty                                 using (⊥)
open import Data.Product                               using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Data.Unit                                  using (⊤; tt)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Judgement.Context.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Type                     Univ as T
open import Logic.Type.Context             Univ as TC  hiding (module Simple)
open import Logic.Type.Context.Polarised   Univ as TCP hiding (module Simple; module Polarised; Polarised)
open import Logic.Judgement         Type ⊥ Type as J   
open import Logic.Judgement.Context        Univ as JC  hiding (module Simple)


data Polarised (p : Polarity) : JC.Context → Set ℓ where
  _<⊢_ : ∀ {A} (A⁺ : TCP.Polarised p + A) (B : Type) → Polarised p (A <⊢ B)
  _⊢>_ : ∀ (A : Type) {B} (B⁻ : TCP.Polarised p - B) → Polarised p (A ⊢> B)


module Simple where


  open  JC.Simple using () renaming (_<_> to _<_>ᴶ)
  open TCP.Simple using () renaming (_[_] to _[_]ᶜ; _<_> to _<_>ᶜ)


  -- Apply judgement contexts to types to get judgements
  _[_] : ∀ {p A} → Polarised p A → Type → Judgement
  (A <⊢ B) [ C ] = A [ C ]ᶜ ⊢ B
  (A ⊢> B) [ C ] = A ⊢ B [ C ]ᶜ


  -- Insert context into judgement contexts to get judgement contexts
  _<_> : ∀ {p₁ p₂ J A} → Polarised p₂ J → TCP.Polarised p₁ p₂ A → Polarised p₁ (J < A >ᴶ)
  (A <⊢ B) < C > = A < C >ᶜ <⊢ B
  (A ⊢> B) < C > = A ⊢> B < C >ᶜ
