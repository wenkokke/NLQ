------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.ResMon.Symmetry {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                               Univ
open import Logic.Classical.Ordered.LambekGrishin.Type.Context.Polarised             Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement                   Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement.Context.Polarised Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base                        Univ


infixl 5 _⋈ _⋈′ _⋈ᴶ
infixl 5 _∞ _∞′ _∞ᴶ


_⋈ : Type → Type
el  A ⋈ = el       A
□   A ⋈ = □       (A ⋈)
◇   A ⋈ = ◇       (A ⋈)
₀   A ⋈ = (A ⋈)   ⁰
A   ⁰ ⋈ = ₀       (A ⋈)
₁   A ⋈ = (A ⋈)   ¹
A   ¹ ⋈ = ₁       (A ⋈)
A ⇒ B ⋈ = (B ⋈) ⇐ (A ⋈)
B ⇐ A ⋈ = (A ⋈) ⇒ (B ⋈)
B ⇚ A ⋈ = (A ⋈) ⇛ (B ⋈)
A ⇛ B ⋈ = (B ⋈) ⇚ (A ⋈)
A ⊗ B ⋈ = (B ⋈) ⊗ (A ⋈)
B ⊕ A ⋈ = (A ⋈) ⊕ (B ⋈)


_∞ : Type → Type
el  A ∞ = el       A
□   A ∞ = ◇       (A ∞)
◇   A ∞ = □       (A ∞)
₀   A ∞ = (A ∞)   ¹
A   ⁰ ∞ = ₁       (A ∞)
₁   A ∞ = (A ∞)   ⁰
A   ¹ ∞ = ₀       (A ∞)
A ⊗ B ∞ = (B ∞) ⊕ (A ∞)
A ⇒ B ∞ = (B ∞) ⇚ (A ∞)
B ⇐ A ∞ = (A ∞) ⇛ (B ∞)
B ⊕ A ∞ = (A ∞) ⊗ (B ∞)
B ⇚ A ∞ = (A ∞) ⇒ (B ∞)
A ⇛ B ∞ = (B ∞) ⇐ (A ∞)


_⋈′ : ∀ {p₁ p₂} → Context p₁ p₂ → Context p₁ p₂
[]     ⋈′ = []
□>   A ⋈′ = □> (A ⋈′)
◇>   A ⋈′ = ◇> (A ⋈′)
₀>   A ⋈′ = (A ⋈′) <⁰
A   <⁰ ⋈′ = ₀> (A ⋈′)
₁>   A ⋈′ = (A ⋈′) <¹
A   <¹ ⋈′ = ₁> (A ⋈′)
A ⊗> B ⋈′ = (B ⋈′) <⊗ (A ⋈)
A ⇒> B ⋈′ = (B ⋈′) <⇐ (A ⋈)
B ⇐> A ⋈′ = (A ⋈′) <⇒ (B ⋈)
A <⊗ B ⋈′ = (B ⋈) ⊗> (A ⋈′)
A <⇒ B ⋈′ = (B ⋈) ⇐> (A ⋈′)
B <⇐ A ⋈′ = (A ⋈) ⇒> (B ⋈′)
B ⊕> A ⋈′ = (A ⋈′) <⊕ (B ⋈)
B ⇚> A ⋈′ = (A ⋈′) <⇛ (B ⋈)
A ⇛> B ⋈′ = (B ⋈′) <⇚ (A ⋈)
B <⊕ A ⋈′ = (A ⋈) ⊕> (B ⋈′)
B <⇚ A ⋈′ = (A ⋈) ⇛> (B ⋈′)
A <⇛ B ⋈′ = (B ⋈) ⇚> (A ⋈′)


_∞′ : ∀ {p₁ p₂} → Context p₁ p₂ → Context (~ p₁) (~ p₂)
[]     ∞′ = []
□>   A ∞′ = ◇> (A ∞′)
◇>   A ∞′ = □> (A ∞′)
₀>   A ∞′ = (A ∞′) <¹
A   <⁰ ∞′ = ₁> (A ∞′)
₁>   A ∞′ = (A ∞′) <⁰
A   <¹ ∞′ = ₀> (A ∞′)
A ⊗> B ∞′ = (B ∞′) <⊕ (A ∞)
A ⇒> B ∞′ = (B ∞′) <⇚ (A ∞)
B ⇐> A ∞′ = (A ∞′) <⇛ (B ∞)
A <⊗ B ∞′ = (B ∞) ⊕> (A ∞′)
A <⇒ B ∞′ = (B ∞) ⇚> (A ∞′)
B <⇐ A ∞′ = (A ∞) ⇛> (B ∞′)
B ⊕> A ∞′ = (A ∞′) <⊗ (B ∞)
B ⇚> A ∞′ = (A ∞′) <⇒ (B ∞)
A ⇛> B ∞′ = (B ∞′) <⇐ (A ∞)
B <⊕ A ∞′ = (A ∞) ⊗> (B ∞′)
B <⇚ A ∞′ = (A ∞) ⇒> (B ∞′)
A <⇛ B ∞′ = (B ∞) ⇐> (A ∞′)


⋈-over-[] : ∀ {p₁ p₂} (A : Context p₁ p₂) {B} → (A [ B ]) ⋈ ≡ (A ⋈′) [ B ⋈ ]
⋈-over-[] []           = refl
⋈-over-[] (□>   A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (◇>   A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (₀>   A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (A   <⁰) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (₁>   A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (A   <¹) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (A ⊗> B) {C} rewrite ⋈-over-[] B {C} = refl
⋈-over-[] (A ⇒> B) {C} rewrite ⋈-over-[] B {C} = refl
⋈-over-[] (B ⇐> A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (A <⊗ B) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (A <⇒ B) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (B <⇐ A) {C} rewrite ⋈-over-[] B {C} = refl
⋈-over-[] (B ⊕> A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (B ⇚> A) {C} rewrite ⋈-over-[] A {C} = refl
⋈-over-[] (A ⇛> B) {C} rewrite ⋈-over-[] B {C} = refl
⋈-over-[] (B <⊕ A) {C} rewrite ⋈-over-[] B {C} = refl
⋈-over-[] (B <⇚ A) {C} rewrite ⋈-over-[] B {C} = refl
⋈-over-[] (A <⇛ B) {C} rewrite ⋈-over-[] A {C} = refl


∞-over-[] : ∀ {p₁ p₂} (A : Context p₁ p₂) {B} → (A [ B ]) ∞ ≡ (A ∞′) [ B ∞ ]
∞-over-[] []           = refl
∞-over-[] (□>   A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (◇>   A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (₀>   A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (A   <⁰) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (₁>   A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (A   <¹) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (A ⊗> B) {C} rewrite ∞-over-[] B {C} = refl
∞-over-[] (A ⇒> B) {C} rewrite ∞-over-[] B {C} = refl
∞-over-[] (B ⇐> A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (A <⊗ B) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (A <⇒ B) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (B <⇐ A) {C} rewrite ∞-over-[] B {C} = refl
∞-over-[] (B ⊕> A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (B ⇚> A) {C} rewrite ∞-over-[] A {C} = refl
∞-over-[] (A ⇛> B) {C} rewrite ∞-over-[] B {C} = refl
∞-over-[] (B <⊕ A) {C} rewrite ∞-over-[] B {C} = refl
∞-over-[] (B <⇚ A) {C} rewrite ∞-over-[] B {C} = refl
∞-over-[] (A <⇛ B) {C} rewrite ∞-over-[] A {C} = refl


_⋈ᴶ : Judgement → Judgement
(A ⊢ B) ⋈ᴶ = A ⋈ ⊢ B ⋈


_∞ᴶ : Judgement → Judgement
(A ⊢ B) ∞ᴶ = B ∞ ⊢ A ∞


_⋈ᴶ′ : ∀ {p} → Contextᴶ p → Contextᴶ p
(A ⊢> B) ⋈ᴶ′ = (A ⋈) ⊢> (B ⋈′)
(A <⊢ B) ⋈ᴶ′ = (A ⋈′) <⊢ (B ⋈)


_∞ᴶ′ : ∀ {p} → Contextᴶ p → Contextᴶ (~ p)
(A ⊢> B) ∞ᴶ′ = (B ∞′) <⊢ (A ∞)
(A <⊢ B) ∞ᴶ′ = (B ∞) ⊢> (A ∞′)


⋈ᴶ-over-[]ᴶ : ∀ {p} (J : Contextᴶ p) {A} → (J [ A ]ᴶ) ⋈ᴶ ≡ (J ⋈ᴶ′) [ A ⋈ ]ᴶ
⋈ᴶ-over-[]ᴶ (A <⊢ B) {C} rewrite ⋈-over-[] A {C} = refl
⋈ᴶ-over-[]ᴶ (A ⊢> B) {C} rewrite ⋈-over-[] B {C} = refl


∞ᴶ-over-[]ᴶ : ∀ {p} (J : Contextᴶ p) {A} → (J [ A ]ᴶ) ∞ᴶ ≡ (J ∞ᴶ′) [ A ∞ ]ᴶ
∞ᴶ-over-[]ᴶ (A <⊢ B) {C} rewrite ∞-over-[] A {C} = refl
∞ᴶ-over-[]ᴶ (A ⊢> B) {C} rewrite ∞-over-[] B {C} = refl


⋈-inv : (A : Type) → A ⋈ ⋈ ≡ A
⋈-inv (el  A)                           = refl
⋈-inv (□   A) rewrite ⋈-inv A           = refl
⋈-inv (◇   A) rewrite ⋈-inv A           = refl
⋈-inv (₀   A) rewrite ⋈-inv A           = refl
⋈-inv (A   ⁰) rewrite ⋈-inv A           = refl
⋈-inv (₁   A) rewrite ⋈-inv A           = refl
⋈-inv (A   ¹) rewrite ⋈-inv A           = refl
⋈-inv (A ⇒ B) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (B ⇐ A) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (B ⇚ A) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (A ⇛ B) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (A ⊗ B) rewrite ⋈-inv A | ⋈-inv B = refl
⋈-inv (A ⊕ B) rewrite ⋈-inv A | ⋈-inv B = refl


∞-inv : (A : Type) → A ∞ ∞ ≡ A
∞-inv (el  A)                           = refl
∞-inv (□   A) rewrite ∞-inv A           = refl
∞-inv (◇   A) rewrite ∞-inv A           = refl
∞-inv (₀   A) rewrite ∞-inv A           = refl
∞-inv (A   ⁰) rewrite ∞-inv A           = refl
∞-inv (₁   A) rewrite ∞-inv A           = refl
∞-inv (A   ¹) rewrite ∞-inv A           = refl
∞-inv (A ⇒ B) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (B ⇐ A) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (B ⇚ A) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (A ⇛ B) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (A ⊗ B) rewrite ∞-inv A | ∞-inv B = refl
∞-inv (A ⊕ B) rewrite ∞-inv A | ∞-inv B = refl


⋈ᴶ-inv : (J : Judgement) → J ⋈ᴶ ⋈ᴶ ≡ J
⋈ᴶ-inv (A ⊢ B) rewrite ⋈-inv A | ⋈-inv B = refl


∞ᴶ-inv : (J : Judgement) → J ∞ᴶ ∞ᴶ ≡ J
∞ᴶ-inv (A ⊢ B) rewrite ∞-inv A | ∞-inv B = refl


⋈∞⋈=∞ : (A : Type) → A ⋈ ∞ ⋈ ≡ A ∞
⋈∞⋈=∞ (el  A)                           = refl
⋈∞⋈=∞ (□   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (◇   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (₀   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (A   ⁰) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (₁   A) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (A   ¹) rewrite ⋈∞⋈=∞ A           = refl
⋈∞⋈=∞ (A ⇒ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (B ⇐ A) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (B ⇚ A) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (A ⇛ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (A ⊗ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl
⋈∞⋈=∞ (A ⊕ B) rewrite ⋈∞⋈=∞ A | ⋈∞⋈=∞ B = refl


∞⋈∞=⋈ : (A : Type) → A ∞ ⋈ ∞ ≡ A ⋈
∞⋈∞=⋈ (el  A)                           = refl
∞⋈∞=⋈ (□   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (◇   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (₀   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (A   ⁰) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (₁   A) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (A   ¹) rewrite ∞⋈∞=⋈ A           = refl
∞⋈∞=⋈ (A ⇒ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (B ⇐ A) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (B ⇚ A) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (A ⇛ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (A ⊗ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl
∞⋈∞=⋈ (A ⊕ B) rewrite ∞⋈∞=⋈ A | ∞⋈∞=⋈ B = refl


lemma-⋈ : ∀ {J} → LG J → LG J ⋈ᴶ
lemma-⋈  ax       = ax
lemma-⋈ (m□  f  ) = m□  (lemma-⋈ f)
lemma-⋈ (m◇  f  ) = m◇  (lemma-⋈ f)
lemma-⋈ (r□◇ f  ) = r□◇ (lemma-⋈ f)
lemma-⋈ (r◇□ f  ) = r◇□ (lemma-⋈ f)
lemma-⋈ (m⁰  f  ) = m₀  (lemma-⋈ f)
lemma-⋈ (m₀  f  ) = m⁰  (lemma-⋈ f)
lemma-⋈ (r⁰₀ f  ) = r₀⁰ (lemma-⋈ f)
lemma-⋈ (r₀⁰ f  ) = r⁰₀ (lemma-⋈ f)
lemma-⋈ (m₁  f  ) = m¹  (lemma-⋈ f)
lemma-⋈ (m¹  f  ) = m₁  (lemma-⋈ f)
lemma-⋈ (r¹₁ f  ) = r₁¹ (lemma-⋈ f)
lemma-⋈ (r₁¹ f  ) = r¹₁ (lemma-⋈ f)
lemma-⋈ (m⊗  f g) = m⊗  (lemma-⋈ g) (lemma-⋈ f)
lemma-⋈ (m⇒  f g) = m⇐  (lemma-⋈ g) (lemma-⋈ f)
lemma-⋈ (m⇐  f g) = m⇒  (lemma-⋈ g) (lemma-⋈ f)
lemma-⋈ (r⇒⊗ f  ) = r⇐⊗ (lemma-⋈ f)
lemma-⋈ (r⊗⇒ f  ) = r⊗⇐ (lemma-⋈ f)
lemma-⋈ (r⇐⊗ f  ) = r⇒⊗ (lemma-⋈ f)
lemma-⋈ (r⊗⇐ f  ) = r⊗⇒ (lemma-⋈ f)
lemma-⋈ (m⊕  f g) = m⊕  (lemma-⋈ g) (lemma-⋈ f)
lemma-⋈ (m⇛  f g) = m⇚  (lemma-⋈ g) (lemma-⋈ f)
lemma-⋈ (m⇚  f g) = m⇛  (lemma-⋈ g) (lemma-⋈ f)
lemma-⋈ (r⇛⊕ f  ) = r⇚⊕ (lemma-⋈ f)
lemma-⋈ (r⊕⇛ f  ) = r⊕⇚ (lemma-⋈ f)
lemma-⋈ (r⊕⇚ f  ) = r⊕⇛ (lemma-⋈ f)
lemma-⋈ (r⇚⊕ f  ) = r⇛⊕ (lemma-⋈ f)
lemma-⋈ (d⇛⇐ f  ) = d⇚⇒ (lemma-⋈ f)
lemma-⋈ (d⇛⇒ f  ) = d⇚⇐ (lemma-⋈ f)
lemma-⋈ (d⇚⇒ f  ) = d⇛⇐ (lemma-⋈ f)
lemma-⋈ (d⇚⇐ f  ) = d⇛⇒ (lemma-⋈ f)


lemma-∞ : ∀ {J} → LG J → LG J ∞ᴶ
lemma-∞  ax       = ax
lemma-∞ (m□  f  ) = m◇  (lemma-∞ f)
lemma-∞ (m◇  f  ) = m□  (lemma-∞ f)
lemma-∞ (r□◇ f  ) = r◇□ (lemma-∞ f)
lemma-∞ (r◇□ f  ) = r□◇ (lemma-∞ f)
lemma-∞ (m⁰  f  ) = m₁  (lemma-∞ f)
lemma-∞ (m₀  f  ) = m¹  (lemma-∞ f)
lemma-∞ (r⁰₀ f  ) = r₁¹ (lemma-∞ f)
lemma-∞ (r₀⁰ f  ) = r¹₁ (lemma-∞ f)
lemma-∞ (m₁  f  ) = m⁰  (lemma-∞ f)
lemma-∞ (m¹  f  ) = m₀  (lemma-∞ f)
lemma-∞ (r¹₁ f  ) = r₀⁰ (lemma-∞ f)
lemma-∞ (r₁¹ f  ) = r⁰₀ (lemma-∞ f)
lemma-∞ (m⊗  f g) = m⊕  (lemma-∞ g) (lemma-∞ f)
lemma-∞ (m⇒  f g) = m⇚  (lemma-∞ g) (lemma-∞ f)
lemma-∞ (m⇐  f g) = m⇛  (lemma-∞ g) (lemma-∞ f)
lemma-∞ (r⇒⊗ f  ) = r⇚⊕ (lemma-∞ f)
lemma-∞ (r⊗⇒ f  ) = r⊕⇚ (lemma-∞ f)
lemma-∞ (r⇐⊗ f  ) = r⇛⊕ (lemma-∞ f)
lemma-∞ (r⊗⇐ f  ) = r⊕⇛ (lemma-∞ f)
lemma-∞ (m⊕  f g) = m⊗  (lemma-∞ g) (lemma-∞ f)
lemma-∞ (m⇛  f g) = m⇐  (lemma-∞ g) (lemma-∞ f)
lemma-∞ (m⇚  f g) = m⇒  (lemma-∞ g) (lemma-∞ f)
lemma-∞ (r⇛⊕ f  ) = r⇐⊗ (lemma-∞ f)
lemma-∞ (r⊕⇛ f  ) = r⊗⇐ (lemma-∞ f)
lemma-∞ (r⊕⇚ f  ) = r⊗⇒ (lemma-∞ f)
lemma-∞ (r⇚⊕ f  ) = r⇒⊗ (lemma-∞ f)
lemma-∞ (d⇛⇐ f  ) = d⇛⇐ (lemma-∞ f)
lemma-∞ (d⇛⇒ f  ) = d⇚⇐ (lemma-∞ f)
lemma-∞ (d⇚⇒ f  ) = d⇚⇒ (lemma-∞ f)
lemma-∞ (d⇚⇐ f  ) = d⇛⇒ (lemma-∞ f)
