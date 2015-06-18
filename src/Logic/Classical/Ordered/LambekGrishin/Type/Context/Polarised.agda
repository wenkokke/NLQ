------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra                                    using (Monoid)
open import Function                                   using (flip; _∘_)
open import Data.Product                               using (∃; _×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type Atom


infixl 50 _[_]
infixr 30 _⊗>_ _<⊗_
infixr 20 _⇛>_ _<⇛_
infixl 20 _⇚>_ _<⇚_
infixr 30 _⊕>_ _<⊕_
infixr 20 _⇒>_ _<⇒_
infixl 20 _⇐>_ _<⇐_
infixr 40 □>_ ◇>_
infixr 40 ₀>_ ₁>_
infixl 40 _<⁰ _<¹




data Context (p : Polarity) : Polarity → Set ℓ where
  []    : Context p p
  □>_   : Context p -  → Context p -
  ◇>_   : Context p +  → Context p +
  ₀>_   : Context p +  → Context p -
  _<⁰   : Context p +  → Context p -
  ₁>_   : Context p -  → Context p +
  _<¹   : Context p -  → Context p +
  _⊗>_  : Type         → Context p +  → Context p +
  _⇒>_  : Type         → Context p -  → Context p -
  _⇐>_  : Type         → Context p +  → Context p -
  _<⊗_  : Context p +  → Type         → Context p +
  _<⇒_  : Context p +  → Type         → Context p -
  _<⇐_  : Context p -  → Type         → Context p -
  _⊕>_  : Type         → Context p -  → Context p -
  _⇚>_  : Type         → Context p -  → Context p +
  _⇛>_  : Type         → Context p +  → Context p +
  _<⊕_  : Context p -  → Type         → Context p -
  _<⇚_  : Context p +  → Type         → Context p +
  _<⇛_  : Context p -  → Type         → Context p +



_[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
[]        [ A ] = A
(□>   B)  [ A ] = □ (B [ A ])
(◇>   B)  [ A ] = ◇ (B [ A ])
(₀>   B)  [ A ] = ₀ (B [ A ])
(₁>   B)  [ A ] = ₁ (B [ A ])
(B   <⁰)  [ A ] = (B [ A ]) ⁰
(B   <¹)  [ A ] = (B [ A ]) ¹
(B ⊗> C)  [ A ] = B ⊗ (C [ A ])
(C <⊗ B)  [ A ] = (C [ A ]) ⊗ B
(B ⇒> C)  [ A ] = B ⇒ (C [ A ])
(C <⇒ B)  [ A ] = (C [ A ]) ⇒ B
(B ⇐> C)  [ A ] = B ⇐ (C [ A ])
(C <⇐ B)  [ A ] = (C [ A ]) ⇐ B
(B ⊕> C)  [ A ] = B ⊕ (C [ A ])
(C <⊕ B)  [ A ] = (C [ A ]) ⊕ B
(B ⇚> C)  [ A ] = B ⇚ (C [ A ])
(C <⇚ B)  [ A ] = (C [ A ]) ⇚ B
(B ⇛> C)  [ A ] = B ⇛ (C [ A ])
(C <⇛ B)  [ A ] = (C [ A ]) ⇛ B



-- Symmetries

infixl 5 _⋈ᶜ _∞ᶜ


_⋈ᶜ : ∀ {p₁ p₂} → Context p₁ p₂ → Context p₁ p₂
([]    ) ⋈ᶜ = []
(□>   A) ⋈ᶜ = □> (A ⋈ᶜ)
(◇>   A) ⋈ᶜ = ◇> (A ⋈ᶜ)
(₀>   A) ⋈ᶜ = (A ⋈ᶜ) <⁰
(A   <⁰) ⋈ᶜ = ₀> (A ⋈ᶜ)
(₁>   A) ⋈ᶜ = (A ⋈ᶜ) <¹
(A   <¹) ⋈ᶜ = ₁> (A ⋈ᶜ)
(A ⊗> B) ⋈ᶜ = (B ⋈ᶜ) <⊗ (A ⋈)
(A ⇒> B) ⋈ᶜ = (B ⋈ᶜ) <⇐ (A ⋈)
(B ⇐> A) ⋈ᶜ = (A ⋈ᶜ) <⇒ (B ⋈)
(A <⊗ B) ⋈ᶜ = (B ⋈) ⊗> (A ⋈ᶜ)
(A <⇒ B) ⋈ᶜ = (B ⋈) ⇐> (A ⋈ᶜ)
(B <⇐ A) ⋈ᶜ = (A ⋈) ⇒> (B ⋈ᶜ)
(B ⊕> A) ⋈ᶜ = (A ⋈ᶜ) <⊕ (B ⋈)
(B ⇚> A) ⋈ᶜ = (A ⋈ᶜ) <⇛ (B ⋈)
(A ⇛> B) ⋈ᶜ = (B ⋈ᶜ) <⇚ (A ⋈)
(B <⊕ A) ⋈ᶜ = (A ⋈) ⊕> (B ⋈ᶜ)
(B <⇚ A) ⋈ᶜ = (A ⋈) ⇛> (B ⋈ᶜ)
(A <⇛ B) ⋈ᶜ = (B ⋈) ⇚> (A ⋈ᶜ)


_∞ᶜ : ∀ {p₁ p₂} → Context p₁ p₂ → Context (~ p₁) (~ p₂)
([]    ) ∞ᶜ = []
(□>   A) ∞ᶜ = ◇> (A ∞ᶜ)
(◇>   A) ∞ᶜ = □> (A ∞ᶜ)
(₀>   A) ∞ᶜ = (A ∞ᶜ) <¹
(A   <⁰) ∞ᶜ = ₁> (A ∞ᶜ)
(₁>   A) ∞ᶜ = (A ∞ᶜ) <⁰
(A   <¹) ∞ᶜ = ₀> (A ∞ᶜ)
(A ⊗> B) ∞ᶜ = (B ∞ᶜ) <⊕ (A ∞)
(A ⇒> B) ∞ᶜ = (B ∞ᶜ) <⇚ (A ∞)
(B ⇐> A) ∞ᶜ = (A ∞ᶜ) <⇛ (B ∞)
(A <⊗ B) ∞ᶜ = (B ∞) ⊕> (A ∞ᶜ)
(A <⇒ B) ∞ᶜ = (B ∞) ⇚> (A ∞ᶜ)
(B <⇐ A) ∞ᶜ = (A ∞) ⇛> (B ∞ᶜ)
(B ⊕> A) ∞ᶜ = (A ∞ᶜ) <⊗ (B ∞)
(B ⇚> A) ∞ᶜ = (A ∞ᶜ) <⇒ (B ∞)
(A ⇛> B) ∞ᶜ = (B ∞ᶜ) <⇐ (A ∞)
(B <⊕ A) ∞ᶜ = (A ∞) ⊗> (B ∞ᶜ)
(B <⇚ A) ∞ᶜ = (A ∞) ⇒> (B ∞ᶜ)
(A <⇛ B) ∞ᶜ = (B ∞) ⇐> (A ∞ᶜ)


⋈-resp-[] : ∀ {p₁ p₂} (A : Context p₁ p₂) {B} → (A [ B ]) ⋈ ≡ (A ⋈ᶜ) [ B ⋈ ]
⋈-resp-[] []           = refl
⋈-resp-[] (□>   A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (◇>   A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (₀>   A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (A   <⁰) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (₁>   A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (A   <¹) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (A ⊗> B) {C} rewrite ⋈-resp-[] B {C} = refl
⋈-resp-[] (A ⇒> B) {C} rewrite ⋈-resp-[] B {C} = refl
⋈-resp-[] (B ⇐> A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (A <⊗ B) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (A <⇒ B) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (B <⇐ A) {C} rewrite ⋈-resp-[] B {C} = refl
⋈-resp-[] (B ⊕> A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (B ⇚> A) {C} rewrite ⋈-resp-[] A {C} = refl
⋈-resp-[] (A ⇛> B) {C} rewrite ⋈-resp-[] B {C} = refl
⋈-resp-[] (B <⊕ A) {C} rewrite ⋈-resp-[] B {C} = refl
⋈-resp-[] (B <⇚ A) {C} rewrite ⋈-resp-[] B {C} = refl
⋈-resp-[] (A <⇛ B) {C} rewrite ⋈-resp-[] A {C} = refl


∞-resp-[] : ∀ {p₁ p₂} (A : Context p₁ p₂) {B} → (A [ B ]) ∞ ≡ (A ∞ᶜ) [ B ∞ ]
∞-resp-[] []           = refl
∞-resp-[] (□>   A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (◇>   A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (₀>   A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (A   <⁰) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (₁>   A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (A   <¹) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (A ⊗> B) {C} rewrite ∞-resp-[] B {C} = refl
∞-resp-[] (A ⇒> B) {C} rewrite ∞-resp-[] B {C} = refl
∞-resp-[] (B ⇐> A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (A <⊗ B) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (A <⇒ B) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (B <⇐ A) {C} rewrite ∞-resp-[] B {C} = refl
∞-resp-[] (B ⊕> A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (B ⇚> A) {C} rewrite ∞-resp-[] A {C} = refl
∞-resp-[] (A ⇛> B) {C} rewrite ∞-resp-[] B {C} = refl
∞-resp-[] (B <⊕ A) {C} rewrite ∞-resp-[] B {C} = refl
∞-resp-[] (B <⇚ A) {C} rewrite ∞-resp-[] B {C} = refl
∞-resp-[] (A <⇛ B) {C} rewrite ∞-resp-[] A {C} = refl
