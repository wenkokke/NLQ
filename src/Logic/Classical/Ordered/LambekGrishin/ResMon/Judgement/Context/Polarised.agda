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


module Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.Context.Polarised {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                     Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised   Univ as TCP
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement         Univ



data Contextᴶ (p : Polarity) : Set ℓ where
  _<⊢_  : Context p +  → Type         → Contextᴶ p
  _⊢>_  : Type         → Context p -  → Contextᴶ p



_[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
(A <⊢ B) [ C ]ᴶ = A [ C ] ⊢ B
(A ⊢> B) [ C ]ᴶ = A ⊢ B [ C ]


_⋈ᴶᶜ : ∀ {p} → Contextᴶ p → Contextᴶ p
(A ⊢> B) ⋈ᴶᶜ = (A ⋈) ⊢> (B ⋈ᶜ)
(A <⊢ B) ⋈ᴶᶜ = (A ⋈ᶜ) <⊢ (B ⋈)


_∞ᴶᶜ : ∀ {p} → Contextᴶ p → Contextᴶ (~ p)
(A ⊢> B) ∞ᴶᶜ = (B ∞ᶜ) <⊢ (A ∞)
(A <⊢ B) ∞ᴶᶜ = (B ∞) ⊢> (A ∞ᶜ)


⋈ᴶ-resp-[]ᴶ : ∀ {p} (J : Contextᴶ p) {A} → (J [ A ]ᴶ) ⋈ᴶ ≡ (J ⋈ᴶᶜ) [ A ⋈ ]ᴶ
⋈ᴶ-resp-[]ᴶ (A <⊢ B) {C} rewrite ⋈-resp-[] A {C} = refl
⋈ᴶ-resp-[]ᴶ (A ⊢> B) {C} rewrite ⋈-resp-[] B {C} = refl


∞ᴶ-resp-[]ᴶ : ∀ {p} (J : Contextᴶ p) {A} → (J [ A ]ᴶ) ∞ᴶ ≡ (J ∞ᴶᶜ) [ A ∞ ]ᴶ
∞ᴶ-resp-[]ᴶ (A <⊢ B) {C} rewrite ∞-resp-[] A {C} = refl
∞ᴶ-resp-[]ᴶ (A ⊢> B) {C} rewrite ∞-resp-[] B {C} = refl
