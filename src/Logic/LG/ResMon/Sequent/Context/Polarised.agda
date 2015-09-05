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


module Logic.LG.ResMon.Sequent.Context.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.LG.Type                     Atom as T
open import Logic.LG.Type.Context.Polarised   Atom as TCP
open import Logic.LG.ResMon.Sequent         Atom


infix 50 _[_]ʲ
infix 3 _<⊢_ _⊢>_


data Contextʲ (p : Polarity) : Set ℓ where
  _<⊢_  : Context p +  → Type         → Contextʲ p
  _⊢>_  : Type         → Context p -  → Contextʲ p



_[_]ʲ : ∀ {p} → Contextʲ p → Type → Sequent
(A <⊢ B) [ C ]ʲ = A [ C ] ⊢ B
(A ⊢> B) [ C ]ʲ = A ⊢ B [ C ]


_⋈ʲᶜ : ∀ {p} → Contextʲ p → Contextʲ p
(A ⊢> B) ⋈ʲᶜ = (A ⋈) ⊢> (B ⋈ᶜ)
(A <⊢ B) ⋈ʲᶜ = (A ⋈ᶜ) <⊢ (B ⋈)


_∞ʲᶜ : ∀ {p} → Contextʲ p → Contextʲ (~ p)
(A ⊢> B) ∞ʲᶜ = (B ∞ᶜ) <⊢ (A ∞)
(A <⊢ B) ∞ʲᶜ = (B ∞) ⊢> (A ∞ᶜ)


⋈ʲ-resp-[]ʲ : ∀ {p} (J : Contextʲ p) {A} → ((J [ A ]ʲ) ⋈ʲ) ≡ ((J ⋈ʲᶜ) [ A ⋈ ]ʲ)
⋈ʲ-resp-[]ʲ (A <⊢ B) {C} rewrite ⋈-resp-[] A {C} = refl
⋈ʲ-resp-[]ʲ (A ⊢> B) {C} rewrite ⋈-resp-[] B {C} = refl


∞ʲ-resp-[]ʲ : ∀ {p} (J : Contextʲ p) {A} → ((J [ A ]ʲ) ∞ʲ) ≡ ((J ∞ʲᶜ) [ A ∞ ]ʲ)
∞ʲ-resp-[]ʲ (A <⊢ B) {C} rewrite ∞-resp-[] A {C} = refl
∞ʲ-resp-[]ʲ (A ⊢> B) {C} rewrite ∞-resp-[] B {C} = refl
