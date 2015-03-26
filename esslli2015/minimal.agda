module minimal {ℓ} (Univ : Set ℓ) where


open import Relation.Binary.PropositionalEquality using (_≡_; refl)


infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇚_
infixr 25 _⇛_
infixr 30 _⊗_
infixr 30 _⊕_


-- Types, Judgements, Base System

data Type : Set ℓ where

  el  : Univ → Type

  _⊗_ : Type → Type → Type
  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type

  _⊕_ : Type → Type → Type
  _⇚_ : Type → Type → Type
  _⇛_ : Type → Type → Type


data Judgement : Set ℓ where
  _⊢_ : Type → Type → Judgement


infix 1 LG_

data LG_ : Judgement → Set ℓ where

  ax  : ∀ {A}       → LG el A ⊢ el A

  -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
  m⊗  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⊗ C ⊢ B ⊗ D
  m⇒  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG B ⇒ C ⊢ A ⇒ D
  m⇐  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⇐ D ⊢ B ⇐ C
  r⇒⊗ : ∀ {A B C}   → LG B ⊢ A ⇒ C → LG A ⊗ B ⊢ C
  r⊗⇒ : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG B ⊢ A ⇒ C
  r⇐⊗ : ∀ {A B C}   → LG A ⊢ C ⇐ B → LG A ⊗ B ⊢ C
  r⊗⇐ : ∀ {A B C}   → LG A ⊗ B ⊢ C → LG A ⊢ C ⇐ B

  -- rules for residuation and monotonicity for (⇚ , ⊕ , ⇛)
  m⊕  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⊕ C ⊢ B ⊕ D
  m⇛  : ∀ {A B C D} → LG C ⊢ D     → LG A ⊢ B     → LG D ⇛ A ⊢ C ⇛ B
  m⇚  : ∀ {A B C D} → LG A ⊢ B     → LG C ⊢ D     → LG A ⇚ D ⊢ B ⇚ C
  r⇛⊕ : ∀ {A B C}   → LG B ⇛ C ⊢ A → LG C ⊢ B ⊕ A
  r⊕⇛ : ∀ {A B C}   → LG C ⊢ B ⊕ A → LG B ⇛ C ⊢ A
  r⊕⇚ : ∀ {A B C}   → LG C ⊢ B ⊕ A → LG C ⇚ A ⊢ B
  r⇚⊕ : ∀ {A B C}   → LG C ⇚ A ⊢ B → LG C ⊢ B ⊕ A

  -- grishin distributives
  d⇛⇐ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG C ⇛ A ⊢ D ⇐ B
  d⇛⇒ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG C ⇛ B ⊢ A ⇒ D
  d⇚⇒ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG B ⇚ D ⊢ A ⇒ C
  d⇚⇐ : ∀ {A B C D} → LG A ⊗ B ⊢ C ⊕ D → LG A ⇚ D ⊢ C ⇐ B



-- Derived Theorems

ax′ : ∀ {A} → LG A ⊢ A
ax′ {el  _} = ax
ax′ {_ ⊗ _} = m⊗ ax′ ax′
ax′ {_ ⇚ _} = m⇚ ax′ ax′
ax′ {_ ⇛ _} = m⇛ ax′ ax′
ax′ {_ ⊕ _} = m⊕ ax′ ax′
ax′ {_ ⇐ _} = m⇐ ax′ ax′
ax′ {_ ⇒ _} = m⇒ ax′ ax′

appl-⇒′ : ∀ {A B} → LG A ⊗ (A ⇒ B) ⊢ B
appl-⇒′ = r⇒⊗ (m⇒ ax′ ax′)

appl-⇐′ : ∀ {A B} → LG (B ⇐ A) ⊗ A ⊢ B
appl-⇐′ = r⇐⊗ (m⇐ ax′ ax′)

appl-⇛′ : ∀ {A B} → LG B ⊢ A ⊕ (A ⇛ B)
appl-⇛′ = r⇛⊕ (m⇛ ax′ ax′)

appl-⇚′ : ∀ {A B} → LG B ⊢ (B ⇚ A) ⊕ A
appl-⇚′ = r⇚⊕ (m⇚ ax′ ax′)



-- First-Class Derivations

infix 1 LG_⋯_

data LG_⋯_ : (I J : Judgement) → Set ℓ where

  []  : ∀ {J}         → LG J ⋯ J

  -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
  r⇒⊗ : ∀ {J A B C}   → LG J ⋯ B ⊢ A ⇒ C → LG J ⋯ A ⊗ B ⊢ C
  r⊗⇒ : ∀ {J A B C}   → LG J ⋯ A ⊗ B ⊢ C → LG J ⋯ B ⊢ A ⇒ C
  r⇐⊗ : ∀ {J A B C}   → LG J ⋯ A ⊢ C ⇐ B → LG J ⋯ A ⊗ B ⊢ C
  r⊗⇐ : ∀ {J A B C}   → LG J ⋯ A ⊗ B ⊢ C → LG J ⋯ A ⊢ C ⇐ B
  m⊗ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⊗ C ⊢ B ⊗ D
  m⊗ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⊗ C ⊢ B ⊗ D
  m⇒ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ B ⇒ C ⊢ A ⇒ D
  m⇒ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ B ⇒ C ⊢ A ⇒ D
  m⇐ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⇐ D ⊢ B ⇐ C
  m⇐ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⇐ D ⊢ B ⇐ C

  -- rules for residuation and monotonicity for (⇚ , ⊕ , ⇛)
  r⇛⊕ : ∀ {J A B C}   → LG J ⋯ B ⇛ C ⊢ A → LG J ⋯ C ⊢ B ⊕ A
  r⊕⇛ : ∀ {J A B C}   → LG J ⋯ C ⊢ B ⊕ A → LG J ⋯ B ⇛ C ⊢ A
  r⊕⇚ : ∀ {J A B C}   → LG J ⋯ C ⊢ B ⊕ A → LG J ⋯ C ⇚ A ⊢ B
  r⇚⊕ : ∀ {J A B C}   → LG J ⋯ C ⇚ A ⊢ B → LG J ⋯ C ⊢ B ⊕ A
  m⊕ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⊕ C ⊢ B ⊕ D
  m⊕ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⊕ C ⊢ B ⊕ D
  m⇛ᴸ : ∀ {J A B C D} → LG J ⋯ C ⊢ D → LG A ⊢ B → LG J ⋯ D ⇛ A ⊢ C ⇛ B
  m⇛ᴿ : ∀ {J A B C D} → LG C ⊢ D → LG J ⋯ A ⊢ B → LG J ⋯ D ⇛ A ⊢ C ⇛ B
  m⇚ᴸ : ∀ {J A B C D} → LG J ⋯ A ⊢ B → LG C ⊢ D → LG J ⋯ A ⇚ D ⊢ B ⇚ C
  m⇚ᴿ : ∀ {J A B C D} → LG A ⊢ B → LG J ⋯ C ⊢ D → LG J ⋯ A ⇚ D ⊢ B ⇚ C

  -- grishin distributives
  d⇛⇐ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ C ⇛ A ⊢ D ⇐ B
  d⇛⇒ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ C ⇛ B ⊢ A ⇒ D
  d⇚⇒ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ B ⇚ D ⊢ A ⇒ C
  d⇚⇐ : ∀ {J A B C D} → LG J ⋯ A ⊗ B ⊢ C ⊕ D → LG J ⋯ A ⇚ D ⊢ C ⇐ B


_$_ : ∀ {I J} → LG I ⋯ J → LG I → LG J
[]      $ x = x
r⇒⊗ f   $ x = r⇒⊗ (f $ x)
r⊗⇒ f   $ x = r⊗⇒ (f $ x)
r⇐⊗ f   $ x = r⇐⊗ (f $ x)
r⊗⇐ f   $ x = r⊗⇐ (f $ x)
m⊗ᴸ f g $ x = m⊗ (f $ x) g
m⊗ᴿ f g $ x = m⊗ f (g $ x)
m⇒ᴸ f g $ x = m⇒ (f $ x) g
m⇒ᴿ f g $ x = m⇒ f (g $ x)
m⇐ᴸ f g $ x = m⇐ (f $ x) g
m⇐ᴿ f g $ x = m⇐ f (g $ x)
r⇛⊕ f   $ x = r⇛⊕ (f $ x)
r⊕⇛ f   $ x = r⊕⇛ (f $ x)
r⊕⇚ f   $ x = r⊕⇚ (f $ x)
r⇚⊕ f   $ x = r⇚⊕ (f $ x)
m⊕ᴸ f g $ x = m⊕ (f $ x) g
m⊕ᴿ f g $ x = m⊕ f (g $ x)
m⇛ᴸ f g $ x = m⇛ (f $ x) g
m⇛ᴿ f g $ x = m⇛ f (g $ x)
m⇚ᴸ f g $ x = m⇚ (f $ x) g
m⇚ᴿ f g $ x = m⇚ f (g $ x)
d⇛⇐ f   $ x = d⇛⇐ (f $ x)
d⇛⇒ f   $ x = d⇛⇒ (f $ x)
d⇚⇒ f   $ x = d⇚⇒ (f $ x)
d⇚⇐ f   $ x = d⇚⇐ (f $ x)


_∘_ : ∀ {I J K} → LG J ⋯ K → LG I ⋯ J → LG I ⋯ K
[]      ∘ h = h
r⇒⊗ f   ∘ h = r⇒⊗ (f ∘ h)
r⊗⇒ f   ∘ h = r⊗⇒ (f ∘ h)
r⇐⊗ f   ∘ h = r⇐⊗ (f ∘ h)
r⊗⇐ f   ∘ h = r⊗⇐ (f ∘ h)
m⊗ᴸ f g ∘ h = m⊗ᴸ (f ∘ h) g
m⊗ᴿ f g ∘ h = m⊗ᴿ f (g ∘ h)
m⇒ᴸ f g ∘ h = m⇒ᴸ (f ∘ h) g
m⇒ᴿ f g ∘ h = m⇒ᴿ f (g ∘ h)
m⇐ᴸ f g ∘ h = m⇐ᴸ (f ∘ h) g
m⇐ᴿ f g ∘ h = m⇐ᴿ f (g ∘ h)
r⇛⊕ f   ∘ h = r⇛⊕ (f ∘ h)
r⊕⇛ f   ∘ h = r⊕⇛ (f ∘ h)
r⊕⇚ f   ∘ h = r⊕⇚ (f ∘ h)
r⇚⊕ f   ∘ h = r⇚⊕ (f ∘ h)
m⊕ᴸ f g ∘ h = m⊕ᴸ (f ∘ h) g
m⊕ᴿ f g ∘ h = m⊕ᴿ f (g ∘ h)
m⇛ᴸ f g ∘ h = m⇛ᴸ (f ∘ h) g
m⇛ᴿ f g ∘ h = m⇛ᴿ f (g ∘ h)
m⇚ᴸ f g ∘ h = m⇚ᴸ (f ∘ h) g
m⇚ᴿ f g ∘ h = m⇚ᴿ f (g ∘ h)
d⇛⇐ f   ∘ h = d⇛⇐ (f ∘ h)
d⇛⇒ f   ∘ h = d⇛⇒ (f ∘ h)
d⇚⇒ f   ∘ h = d⇚⇒ (f ∘ h)
d⇚⇐ f   ∘ h = d⇚⇐ (f ∘ h)


∘-def : ∀ {I J K} (f : LG I ⋯ J) (g : LG J ⋯ K) (x : LG I)
      → g $ (f $ x) ≡ (g ∘ f) $ x
∘-def f []        x = refl
∘-def f (r⇒⊗ g)   x rewrite ∘-def f g x = refl
∘-def f (r⊗⇒ g)   x rewrite ∘-def f g x = refl
∘-def f (r⇐⊗ g)   x rewrite ∘-def f g x = refl
∘-def f (r⊗⇐ g)   x rewrite ∘-def f g x = refl
∘-def f (m⊗ᴸ g h) x rewrite ∘-def f g x = refl
∘-def f (m⊗ᴿ g h) x rewrite ∘-def f h x = refl
∘-def f (m⇒ᴸ g h) x rewrite ∘-def f g x = refl
∘-def f (m⇒ᴿ g h) x rewrite ∘-def f h x = refl
∘-def f (m⇐ᴸ g h) x rewrite ∘-def f g x = refl
∘-def f (m⇐ᴿ g h) x rewrite ∘-def f h x = refl
∘-def f (r⇛⊕ g)   x rewrite ∘-def f g x = refl
∘-def f (r⊕⇛ g)   x rewrite ∘-def f g x = refl
∘-def f (r⊕⇚ g)   x rewrite ∘-def f g x = refl
∘-def f (r⇚⊕ g)   x rewrite ∘-def f g x = refl
∘-def f (m⊕ᴸ g h) x rewrite ∘-def f g x = refl
∘-def f (m⊕ᴿ g h) x rewrite ∘-def f h x = refl
∘-def f (m⇛ᴸ g h) x rewrite ∘-def f g x = refl
∘-def f (m⇛ᴿ g h) x rewrite ∘-def f h x = refl
∘-def f (m⇚ᴸ g h) x rewrite ∘-def f g x = refl
∘-def f (m⇚ᴿ g h) x rewrite ∘-def f h x = refl
∘-def f (d⇛⇐ g)   x rewrite ∘-def f g x = refl
∘-def f (d⇛⇒ g)   x rewrite ∘-def f g x = refl
∘-def f (d⇚⇒ g)   x rewrite ∘-def f g x = refl
∘-def f (d⇚⇐ g)   x rewrite ∘-def f g x = refl



-- Formula Contexts

data Context : Set ℓ where
  []   : Context
  _⊗>_ : Type → Context → Context
  _⇒>_ : Type → Context → Context
  _⇐>_ : Type → Context → Context
  _<⊗_ : Context → Type → Context
  _<⇒_ : Context → Type → Context
  _<⇐_ : Context → Type → Context
  _⊕>_ : Type → Context → Context
  _⇚>_ : Type → Context → Context
  _⇛>_ : Type → Context → Context
  _<⊕_ : Context → Type → Context
  _<⇚_ : Context → Type → Context
  _<⇛_ : Context → Type → Context


_[_] : Context → Type → Type
[]       [ A ] = A
(B ⊗> C) [ A ] = B ⊗ (C [ A ])
(B ⇒> C) [ A ] = B ⇒ (C [ A ])
(B ⇐> C) [ A ] = B ⇐ (C [ A ])
(B ⊕> C) [ A ] = B ⊕ (C [ A ])
(B ⇛> C) [ A ] = B ⇛ (C [ A ])
(B ⇚> C) [ A ] = B ⇚ (C [ A ])
(C <⊗ B) [ A ] = (C [ A ]) ⊗ B
(C <⇒ B) [ A ] = (C [ A ]) ⇒ B
(C <⇐ B) [ A ] = (C [ A ]) ⇐ B
(C <⊕ B) [ A ] = (C [ A ]) ⊕ B
(C <⇛ B) [ A ] = (C [ A ]) ⇛ B
(C <⇚ B) [ A ] = (C [ A ]) ⇚ B


_<_> : Context → Context → Context
[]       < A > = A
(B ⊗> C) < A > = B ⊗> (C < A >)
(B ⇒> C) < A > = B ⇒> (C < A >)
(B ⇐> C) < A > = B ⇐> (C < A >)
(B ⊕> C) < A > = B ⊕> (C < A >)
(B ⇛> C) < A > = B ⇛> (C < A >)
(B ⇚> C) < A > = B ⇚> (C < A >)
(C <⊗ B) < A > = (C < A >) <⊗ B
(C <⇒ B) < A > = (C < A >) <⇒ B
(C <⇐ B) < A > = (C < A >) <⇐ B
(C <⊕ B) < A > = (C < A >) <⊕ B
(C <⇛ B) < A > = (C < A >) <⇛ B
(C <⇚ B) < A > = (C < A >) <⇚ B



-- Well-Polarised Formula Contexts

data Polarity : Set where
  + : Polarity
  - : Polarity


data Polarised (p : Polarity) : Polarity → Context → Set ℓ where

  []   : Polarised p p []

  _⊗>_ : (A : Type) {B : Context} (B⁺ : Polarised p + B) → Polarised p + (A ⊗> B)
  _⇛>_ : (A : Type) {B : Context} (B⁺ : Polarised p + B) → Polarised p + (A ⇛> B)
  _⇚>_ : (A : Type) {B : Context} (B⁻ : Polarised p - B) → Polarised p + (A ⇚> B)
  _⊕>_ : (A : Type) {B : Context} (B⁻ : Polarised p - B) → Polarised p - (A ⊕> B)
  _⇒>_ : (A : Type) {B : Context} (B⁻ : Polarised p - B) → Polarised p - (A ⇒> B)
  _⇐>_ : (A : Type) {B : Context} (B⁺ : Polarised p + B) → Polarised p - (A ⇐> B)

  _<⊗_ : {A : Context} (A⁺ : Polarised p + A) (B : Type) → Polarised p + (A <⊗ B)
  _<⇛_ : {A : Context} (A⁻ : Polarised p - A) (B : Type) → Polarised p + (A <⇛ B)
  _<⇚_ : {A : Context} (A⁺ : Polarised p + A) (B : Type) → Polarised p + (A <⇚ B)
  _<⊕_ : {A : Context} (A⁻ : Polarised p - A) (B : Type) → Polarised p - (A <⊕ B)
  _<⇒_ : {A : Context} (A⁺ : Polarised p + A) (B : Type) → Polarised p - (A <⇒ B)
  _<⇐_ : {A : Context} (A⁻ : Polarised p - A) (B : Type) → Polarised p - (A <⇐ B)


_[_]ᴾ : ∀ {p₁ p₂ A} → Polarised p₁ p₂ A → Type → Type
[]       [ A ]ᴾ = A
(B ⊗> C) [ A ]ᴾ = B ⊗ (C [ A ]ᴾ)
(B ⇒> C) [ A ]ᴾ = B ⇒ (C [ A ]ᴾ)
(B ⇐> C) [ A ]ᴾ = B ⇐ (C [ A ]ᴾ)
(B ⊕> C) [ A ]ᴾ = B ⊕ (C [ A ]ᴾ)
(B ⇛> C) [ A ]ᴾ = B ⇛ (C [ A ]ᴾ)
(B ⇚> C) [ A ]ᴾ = B ⇚ (C [ A ]ᴾ)
(C <⊗ B) [ A ]ᴾ = (C [ A ]ᴾ) ⊗ B
(C <⇒ B) [ A ]ᴾ = (C [ A ]ᴾ) ⇒ B
(C <⇐ B) [ A ]ᴾ = (C [ A ]ᴾ) ⇐ B
(C <⊕ B) [ A ]ᴾ = (C [ A ]ᴾ) ⊕ B
(C <⇛ B) [ A ]ᴾ = (C [ A ]ᴾ) ⇛ B
(C <⇚ B) [ A ]ᴾ = (C [ A ]ᴾ) ⇚ B


_<_>ᴾ : ∀ {p₁ p₂ p₃ A B} → Polarised p₂ p₃ A → Polarised p₁ p₂ B → Polarised p₁ p₃ (A < B >)
[]       < A >ᴾ = A
(B ⊗> C) < A >ᴾ = B ⊗> (C < A >ᴾ)
(B ⇒> C) < A >ᴾ = B ⇒> (C < A >ᴾ)
(B ⇐> C) < A >ᴾ = B ⇐> (C < A >ᴾ)
(B ⊕> C) < A >ᴾ = B ⊕> (C < A >ᴾ)
(B ⇛> C) < A >ᴾ = B ⇛> (C < A >ᴾ)
(B ⇚> C) < A >ᴾ = B ⇚> (C < A >ᴾ)
(C <⊗ B) < A >ᴾ = (C < A >ᴾ) <⊗ B
(C <⇒ B) < A >ᴾ = (C < A >ᴾ) <⇒ B
(C <⇐ B) < A >ᴾ = (C < A >ᴾ) <⇐ B
(C <⊕ B) < A >ᴾ = (C < A >ᴾ) <⊕ B
(C <⇛ B) < A >ᴾ = (C < A >ᴾ) <⇛ B
(C <⇚ B) < A >ᴾ = (C < A >ᴾ) <⇚ B



-- Judgement Contexts


data Contextᴶ : Set ℓ where
  _<⊢_ : Context → Type → Contextᴶ
  _⊢>_ : Type → Context → Contextᴶ


_[_]ᴶ : Contextᴶ → Type → Judgement
(A <⊢ B) [ C ]ᴶ = A [ C ] ⊢ B
(A ⊢> B) [ C ]ᴶ = A ⊢ B [ C ]


_<_>ᴶ : Contextᴶ → Context → Contextᴶ
_<_>ᴶ (A <⊢ B) C = A < C > <⊢ B
_<_>ᴶ (A ⊢> B) C = A ⊢> B < C >


data Polarisedᴶ (p : Polarity) : Contextᴶ → Set ℓ where
  _<⊢_ : ∀ {A} (A⁺ : Polarised p + A) (B : Type) → Polarisedᴶ p (A <⊢ B)
  _⊢>_ : ∀ (A : Type) {B} (B⁻ : Polarised p - B) → Polarisedᴶ p (A ⊢> B)



-- Origins

module el where

  data Origin {J B} (J⁺ : Polarisedᴶ + J) (f : LG J [ el B ]ᴶ) : Set ℓ where
    origin : (f′ : ∀ {G} → LG G ⊢ el B ⋯ J [ G ]ᴶ)
           → (pr : f ≡ f′ $ ax)
           → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B} (J⁺ : Polarisedᴶ + J) (f : LG J [ el B ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       ax          = origin [] refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (r⊗⇒ [])
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (r⊗⇐ [])
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)     = go ((_ ⇛> []) <⊢ _)       f  (r⇛⊕ [])
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)     = go (([] <⇚ _) <⊢ _)       f  (r⇚⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ el B ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g $ f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin f′ pr rewrite pr | ∘-def f′ g ax = origin (g ∘ f′) refl

module ⊗ where

  data Origin {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⊗ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG E ⊢ B) (h₂ : LG F ⊢ C)
                → (f′ : ∀ {G} → LG E ⊗ F ⊢ G ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ $ m⊗ h₁ h₂)
                → Origin J⁻ f

  mutual
    viewOrigin : ∀ {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⊗ C ]ᴶ) → Origin J⁻ f
    viewOrigin (._ ⊢> [])       (m⊗  f₁ f₂) = origin f₁ f₂ [] refl
    viewOrigin (._ ⊢> [])       (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> []))       f  (r⇒⊗ [])
    viewOrigin (._ ⊢> [])       (r⇐⊗ f)     = go (_ ⊢> ([] <⇐ _))       f  (r⇐⊗ [])
    viewOrigin (._ ⊢> [])       (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> []))       f  (r⊕⇛ [])
    viewOrigin (._ ⊢> [])       (r⊕⇚ f)     = go (_ ⊢> ([] <⊕ _))       f  (r⊕⇚ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B C}
         → (I⁻ : Polarisedᴶ - I) (f : LG I [ B ⊗ C ]ᴶ)
         → {J⁻ : Polarisedᴶ - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁻ (g $ f)
      go I⁻ f {J⁻} g with viewOrigin I⁻ f
      ... | origin h₁ h₂ f′ pr rewrite pr | ∘-def f′ g (m⊗ h₁ h₂) = origin h₁ h₂ (g ∘ f′) refl


module ⇒ where

  data Origin {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇒ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG E ⊢ B) (h₂ : LG C ⊢ F)
                → (f′ : ∀ {G} → LG G ⊢ E ⇒ F ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ $ m⇒ h₁ h₂)
                → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇒ C ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       (m⇒  f₁ f₂) = origin f₁ f₂ [] refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (r⊗⇒ [])
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (r⊗⇐ [])
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)     = go ((_ ⇛> []) <⊢ _)       f  (r⇛⊕ [])
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)     = go (([] <⇚ _) <⊢ _)       f  (r⇚⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B C}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ B ⇒ C ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g $ f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin h₁ h₂ f′ pr rewrite pr | ∘-def f′ g (m⇒ h₁ h₂) = origin h₁ h₂ (g ∘ f′) refl


module ⇐ where

  data Origin {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇐ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG B ⊢ E) (h₂ : LG F ⊢ C)
                → (f′ : ∀ {G} → LG G ⊢ E ⇐ F ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ $ m⇐ h₁ h₂)
                → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇐ C ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       (m⇐  f₁ f₂) = origin f₁ f₂ [] refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (r⊗⇒ [])
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (r⊗⇐ [])
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)     = go ((_ ⇛> []) <⊢ _)       f  (r⇛⊕ [])
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)     = go (([] <⇚ _) <⊢ _)       f  (r⇚⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B C}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ B ⇐ C ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g $ f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin h₁ h₂ f′ pr rewrite pr | ∘-def f′ g (m⇐ h₁ h₂) = origin h₁ h₂ (g ∘ f′) refl

module ⊕ where

  data Origin {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⊕ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG B ⊢ E) (h₂ : LG C ⊢ F)
                → (f′ : ∀ {G} → LG G ⊢ E ⊕ F ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ $ m⊕ h₁ h₂)
                → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⊕ C ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       (m⊕  f₁ f₂) = origin f₁ f₂ [] refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)     = go ((_ ⊗> []) <⊢ _)       f  (r⊗⇒ [])
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)     = go (([] <⊗ _) <⊢ _)       f  (r⊗⇐ [])
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)     = go ((_ ⇛> []) <⊢ _)       f  (r⇛⊕ [])
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)     = go (([] <⇚ _) <⊢ _)       f  (r⇚⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B C}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ B ⊕ C ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g $ f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin h₁ h₂ f′ pr rewrite pr | ∘-def f′ g (m⊕ h₁ h₂) = origin h₁ h₂ (g ∘ f′) refl

module ⇚ where

  data Origin {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇚ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG E ⊢ B) (h₂ : LG C ⊢ F)
                → (f′ : ∀ {G} → LG E ⇚ F ⊢ G ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ $ m⇚ h₁ h₂)
                → Origin J⁻ f

  mutual
    viewOrigin : ∀ {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇚ C ]ᴶ) → Origin J⁻ f
    viewOrigin (._ ⊢> [])       (m⇚  f₁ f₂) = origin f₁ f₂ [] refl
    viewOrigin (._ ⊢> [])       (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> []))       f  (r⇒⊗ [])
    viewOrigin (._ ⊢> [])       (r⇐⊗ f)     = go (_ ⊢> ([] <⇐ _))       f  (r⇐⊗ [])
    viewOrigin (._ ⊢> [])       (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> []))       f  (r⊕⇛ [])
    viewOrigin (._ ⊢> [])       (r⊕⇚ f)     = go (_ ⊢> ([] <⊕ _))       f  (r⊕⇚ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B C}
         → (I⁻ : Polarisedᴶ - I) (f : LG I [ B ⇚ C ]ᴶ)
         → {J⁻ : Polarisedᴶ - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁻ (g $ f)
      go I⁻ f {J⁻} g with viewOrigin I⁻ f
      ... | origin h₁ h₂ f′ pr rewrite pr | ∘-def f′ g (m⇚ h₁ h₂) = origin h₁ h₂ (g ∘ f′) refl

module ⇛ where

  data Origin {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇛ C ]ᴶ) : Set ℓ where
       origin : ∀ {E F}
                → (h₁ : LG B ⊢ E) (h₂ : LG F ⊢ C)
                → (f′ : ∀ {G} → LG E ⇛ F ⊢ G ⋯ J [ G ]ᴶ)
                → (pr : f ≡ f′ $ m⇛ h₁ h₂)
                → Origin J⁻ f

  mutual
    viewOrigin : ∀ {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇛ C ]ᴶ) → Origin J⁻ f
    viewOrigin (._ ⊢> [])       (m⇛  f₁ f₂) = origin f₁ f₂ [] refl
    viewOrigin (._ ⊢> [])       (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> []))       f  (r⇒⊗ [])
    viewOrigin (._ ⊢> [])       (r⇐⊗ f)     = go (_ ⊢> ([] <⇐ _))       f  (r⇐⊗ [])
    viewOrigin (._ ⊢> [])       (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> []))       f  (r⊕⇛ [])
    viewOrigin (._ ⊢> [])       (r⊕⇚ f)     = go (_ ⊢> ([] <⊕ _))       f  (r⊕⇚ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f₁ f₂) = go (B <⊢ _)               f₂ (m⊗ᴿ f₁ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)     = go (B <⊢ _)               f  (r⇒⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⊗> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)     = go (_ ⊢> (_ ⇐> B))        f  (r⇐⊗ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⊗> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⊗> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⊗> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇛> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇛> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f₁ f₂) = go (B <⊢ _)               f₂ (m⇛ᴿ f₁ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇛> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)     = go (B <⊢ _)               f  (r⊕⇛ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇛> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)     = go ((B <⊗ _) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A ⇚> B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)     = go (((A ⇚> B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇚ᴿ f₁ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A ⇚> B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)     = go (_ ⊢> (_ ⊕> B))        f  (r⊕⇚ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)     = go (((A ⇚> B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇒ [])
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇚⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f₁ f₂) = go (A <⊢ _)               f₁ (m⊗ᴸ [] f₂)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)     = go (_ ⊢> (A <⇒ _))        f  (r⇒⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⊗ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)     = go (A <⊢ _)               f  (r⇐⊗ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⊗ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⊗ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⊗ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇛ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇛ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇛ᴸ [] f₂)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇛ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)     = go (_ ⊢> (A <⊕ _))        f  (r⊕⇛ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇛ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇐ [])
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇛⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)     = go ((_ ⊗> (A <⇚ B)) <⊢ _) f  (r⊗⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)     = go (((A <⇚ B) <⊗ _) <⊢ _) f  (r⊗⇐ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f₁ f₂) = go (A <⊢ _)               f₁ (m⇚ᴸ [] f₂)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)     = go ((_ ⇛> (A <⇚ B)) <⊢ _) f  (r⇛⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)     = go (A <⊢ _)               f  (r⊕⇚ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)     = go (((A <⇚ B) <⇚ _) <⊢ _) f  (r⇚⊕ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)     = go ((_ ⊗> A) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⊕> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⊕> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f₁ f₂) = go (_ ⊢> B)               f₂ (m⊕ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)     = go (_ ⊢> B)               f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⊕> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⊕> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)     = go ((_ ⇚> B) <⊢ _)        f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f₁ f₂) = go (_ ⊢> B)               f₂ (m⇒ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇒> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)     = go (_ ⊢> B)               f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇒> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇒> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇒> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)     = go (_ ⊢> (_ ⊕> B))        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)     = go (_ ⊢> (B <⊕ _))        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f₁ f₂) = go (B <⊢ _)               f₂ (m⇐ᴿ f₁ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A ⇐> B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)     = go (_ ⊢> ((A ⇐> B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A ⇐> B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)     = go (_ ⊢> ((A ⇐> B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)     = go ((_ ⊗> B) <⊢ _)        f  (d⇚⇐ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⊕ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⊕ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f₁ f₂) = go (_ ⊢> A)               f₁ (m⊕ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)     = go ((A <⇛ _) <⊢ _)        f  (r⇛⊕ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⊕ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⊕ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)     = go (_ ⊢> A)               f  (r⇚⊕ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f₁ f₂) = go (A <⊢ _)               f₁ (m⇒ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇒ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (r⊗⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇒ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇒ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇒ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇛⇒ [])
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)     = go ((A <⊗ _) <⊢ _)        f  (d⇚⇒ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f₁ f₂) = go (_ ⊢> A)               f₁ (m⇐ᴸ [] f₂)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)     = go (_ ⊢> (_ ⇒> (A <⇐ B))) f  (r⇒⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)     = go (_ ⊢> ((A <⇐ B) <⇐ _)) f  (r⇐⊗ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)     = go (_ ⊢> A)               f  (r⊗⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)     = go (_ ⊢> (_ ⊕> (A <⇐ B))) f  (r⊕⇛ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)     = go (_ ⊢> ((A <⇐ B) <⊕ _)) f  (r⊕⇚ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)     = go (_ ⊢> (_ ⊕> A))        f  (d⇛⇐ [])
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)     = go (_ ⊢> (A <⊕ _))        f  (d⇚⇐ [])

    private
      go : ∀ {I J B C}
         → (I⁻ : Polarisedᴶ - I) (f : LG I [ B ⇛ C ]ᴶ)
         → {J⁻ : Polarisedᴶ - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁻ (g $ f)
      go I⁻ f {J⁻} g with viewOrigin I⁻ f
      ... | origin h₁ h₂ f′ pr rewrite pr | ∘-def f′ g (m⇛ h₁ h₂) = origin h₁ h₂ (g ∘ f′) refl


-- Admissible Transitivity

trans′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el _}  f  g with el.viewOrigin ([] <⊢ _) g
... | el.origin      g′ _ = g′ $ f
trans′ {B = _ ⊗ _} f  g with ⊗.viewOrigin (_ ⊢> []) f
... | ⊗.origin h₁ h₂ f′ _ = f′ $ r⇐⊗ (trans′ h₁ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ g)))))
trans′ {B = _ ⇐ _} f  g with ⇐.viewOrigin ([] <⊢ _) g
... | ⇐.origin h₁ h₂ g′ _ = g′ $ r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ (trans′ (r⇐⊗ f) h₁))))
trans′ {B = _ ⇒ _} f  g with ⇒.viewOrigin ([] <⊢ _) g
... | ⇒.origin h₁ h₂ g′ _ = g′ $ r⊗⇒ (r⇐⊗ (trans′ h₁ (r⊗⇐ (trans′ (r⇒⊗ f) h₂))))
trans′ {B = _ ⊕ _} f  g with ⊕.viewOrigin ([] <⊢ _) g
... | ⊕.origin h₁ h₂ g′ _ = g′ $ r⇚⊕ (trans′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ f) h₂))) h₁)
trans′ {B = _ ⇚ _} f  g with ⇚.viewOrigin (_ ⊢> []) f
... | ⇚.origin h₁ h₂ f′ _ = f′ $ r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ (trans′ h₁ (r⇚⊕ g))) h₂))
trans′ {B = _ ⇛ _} f  g with ⇛.viewOrigin (_ ⊢> []) f
... | ⇛.origin h₁ h₂ f′ _ = f′ $ r⊕⇛ (r⇚⊕ (trans′ (r⊕⇚ (trans′ h₂ (r⇛⊕ g))) h₁))
