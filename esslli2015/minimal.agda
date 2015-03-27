module minimal {ℓ} (Univ : Set ℓ) where


open import Function using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


infixr  20  _⇒_
infixl  20  _⇐_
infixl  25  _⇚_
infixr  25  _⇛_
infixr  30  _⊗_
infixr  30  _⊕_


data Type : Set ℓ where
  el           : Univ  → Type
  _⊗_ _⇒_ _⇐_  : Type  → Type  → Type
  _⊕_ _⇚_ _⇛_  : Type  → Type  → Type


data Judgement : Set ℓ where
  _⊢_  : Type → Type → Judgement


infix 1 LG_

data LG_ : Judgement → Set ℓ where

  ax   : ∀ {A}       →  LG el A ⊢ el A

  -- residuation and monotonicity for (⇐ , ⊗ , ⇒)
  r⇒⊗  : ∀ {A B C}   →  LG B ⊢ A ⇒ C  → LG A ⊗ B ⊢ C
  r⊗⇒  : ∀ {A B C}   →  LG A ⊗ B ⊢ C  → LG B ⊢ A ⇒ C
  r⇐⊗  : ∀ {A B C}   →  LG A ⊢ C ⇐ B  → LG A ⊗ B ⊢ C
  r⊗⇐  : ∀ {A B C}   →  LG A ⊗ B ⊢ C  → LG A ⊢ C ⇐ B

  m⊗   : ∀ {A B C D} →  LG A ⊢ B      → LG C ⊢ D      → LG A ⊗ C ⊢ B ⊗ D
  m⇒   : ∀ {A B C D} →  LG A ⊢ B      → LG C ⊢ D      → LG B ⇒ C ⊢ A ⇒ D
  m⇐   : ∀ {A B C D} →  LG A ⊢ B      → LG C ⊢ D      → LG A ⇐ D ⊢ B ⇐ C

  -- residuation and monotonicity for (⇚ , ⊕ , ⇛)
  r⇛⊕  : ∀ {A B C}   →  LG B ⇛ C ⊢ A  → LG C ⊢ B ⊕ A
  r⊕⇛  : ∀ {A B C}   →  LG C ⊢ B ⊕ A  → LG B ⇛ C ⊢ A
  r⊕⇚  : ∀ {A B C}   →  LG C ⊢ B ⊕ A  → LG C ⇚ A ⊢ B
  r⇚⊕  : ∀ {A B C}   →  LG C ⇚ A ⊢ B  → LG C ⊢ B ⊕ A

  m⊕   : ∀ {A B C D} →  LG A ⊢ B      → LG C ⊢ D      → LG A ⊕ C ⊢ B ⊕ D
  m⇛   : ∀ {A B C D} →  LG C ⊢ D      → LG A ⊢ B      → LG D ⇛ A ⊢ C ⇛ B
  m⇚   : ∀ {A B C D} →  LG A ⊢ B      → LG C ⊢ D      → LG A ⇚ D ⊢ B ⇚ C

  -- grishin distributives
  d⇛⇐  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG C ⇛ A ⊢ D ⇐ B
  d⇛⇒  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG C ⇛ B ⊢ A ⇒ D
  d⇚⇒  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG B ⇚ D ⊢ A ⇒ C
  d⇚⇐  : ∀ {A B C D} →  LG A ⊗ B ⊢ C ⊕ D  → LG A ⇚ D ⊢ C ⇐ B


ax′ : ∀ {A} → LG A ⊢ A
ax′ {el  _} = ax
ax′ {_ ⊗ _} = m⊗ ax′ ax′
ax′ {_ ⇚ _} = m⇚ ax′ ax′
ax′ {_ ⇛ _} = m⇛ ax′ ax′
ax′ {_ ⊕ _} = m⊕ ax′ ax′
ax′ {_ ⇐ _} = m⇐ ax′ ax′
ax′ {_ ⇒ _} = m⇒ ax′ ax′


appl-⇒′  : ∀ {A B} → LG A ⊗ (A ⇒ B) ⊢ B
appl-⇒′  = r⇒⊗ (m⇒ ax′ ax′)

appl-⇐′  : ∀ {A B} → LG (B ⇐ A) ⊗ A ⊢ B
appl-⇐′  = r⇐⊗ (m⇐ ax′ ax′)

appl-⇛′  : ∀ {A B} → LG B ⊢ A ⊕ (A ⇛ B)
appl-⇛′  = r⇛⊕ (m⇛ ax′ ax′)

appl-⇚′  : ∀ {A B} → LG B ⊢ (B ⇚ A) ⊕ A
appl-⇚′  = r⇚⊕ (m⇚ ax′ ax′)


data Context : Set ℓ where
  []              : Context
  _⊗>_ _⇒>_ _⇐>_  : Type     → Context  → Context
  _⊕>_ _⇚>_ _⇛>_  : Type     → Context  → Context
  _<⊗_ _<⇒_ _<⇐_  : Context  → Type     → Context
  _<⊕_ _<⇚_ _<⇛_  : Context  → Type     → Context


_[_] : Context → Type → Type
[]        [ A ] = A
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


_⟨_⟩ : Context → Context → Context
[]        ⟨ A ⟩ = A
(B ⊗> C)  ⟨ A ⟩ = B ⊗> (C ⟨ A ⟩)
(C <⊗ B)  ⟨ A ⟩ = (C ⟨ A ⟩) <⊗ B
(B ⇒> C)  ⟨ A ⟩ = B ⇒> (C ⟨ A ⟩)
(C <⇒ B)  ⟨ A ⟩ = (C ⟨ A ⟩) <⇒ B
(B ⇐> C)  ⟨ A ⟩ = B ⇐> (C ⟨ A ⟩)
(C <⇐ B)  ⟨ A ⟩ = (C ⟨ A ⟩) <⇐ B
(B ⊕> C)  ⟨ A ⟩ = B ⊕> (C ⟨ A ⟩)
(C <⊕ B)  ⟨ A ⟩ = (C ⟨ A ⟩) <⊕ B
(B ⇚> C)  ⟨ A ⟩ = B ⇚> (C ⟨ A ⟩)
(C <⇚ B)  ⟨ A ⟩ = (C ⟨ A ⟩) <⇚ B
(C <⇛ B)  ⟨ A ⟩ = (C ⟨ A ⟩) <⇛ B
(B ⇛> C)  ⟨ A ⟩ = B ⇛> (C ⟨ A ⟩)


data Polarity : Set where
  +  : Polarity
  -  : Polarity


data Polarised (p : Polarity) : Polarity → Context → Set ℓ where
  []    : Polarised p p []
  _⊗>_  : (A : Type) {B : Context} (B⁺ : Polarised p + B)  → Polarised p + (A ⊗> B)
  _⇒>_  : (A : Type) {B : Context} (B⁻ : Polarised p - B)  → Polarised p - (A ⇒> B)
  _⇐>_  : (A : Type) {B : Context} (B⁺ : Polarised p + B)  → Polarised p - (A ⇐> B)
  _<⊗_  : {A : Context} (A⁺ : Polarised p + A) (B : Type)  → Polarised p + (A <⊗ B)
  _<⇒_  : {A : Context} (A⁺ : Polarised p + A) (B : Type)  → Polarised p - (A <⇒ B)
  _<⇐_  : {A : Context} (A⁻ : Polarised p - A) (B : Type)  → Polarised p - (A <⇐ B)
  _⊕>_  : (A : Type) {B : Context} (B⁻ : Polarised p - B)  → Polarised p - (A ⊕> B)
  _⇚>_  : (A : Type) {B : Context} (B⁻ : Polarised p - B)  → Polarised p + (A ⇚> B)
  _⇛>_  : (A : Type) {B : Context} (B⁺ : Polarised p + B)  → Polarised p + (A ⇛> B)
  _<⊕_  : {A : Context} (A⁻ : Polarised p - A) (B : Type)  → Polarised p - (A <⊕ B)
  _<⇚_  : {A : Context} (A⁺ : Polarised p + A) (B : Type)  → Polarised p + (A <⇚ B)
  _<⇛_  : {A : Context} (A⁻ : Polarised p - A) (B : Type)  → Polarised p + (A <⇛ B)


data Contextᴶ : Set ℓ where
  _<⊢_  : Context  → Type     → Contextᴶ
  _⊢>_  : Type     → Context  → Contextᴶ


_[_]ᴶ : Contextᴶ → Type → Judgement
(A <⊢ B) [ C ]ᴶ = A [ C ] ⊢ B
(A ⊢> B) [ C ]ᴶ = A ⊢ B [ C ]


_⟨_⟩ᴶ : Contextᴶ → Context → Contextᴶ
(A <⊢ B) ⟨ C ⟩ᴶ = A ⟨ C ⟩ <⊢ B
(A ⊢> B) ⟨ C ⟩ᴶ = A ⊢> B ⟨ C ⟩


data Polarisedᴶ (p : Polarity) : Contextᴶ → Set ℓ where
  _<⊢_  : {A : Context} (A⁺ : Polarised p + A) (B : Type) → Polarisedᴶ p (A <⊢ B)
  _⊢>_  : (A : Type) {B : Context} (B⁻ : Polarised p - B) → Polarisedᴶ p (A ⊢> B)


LG_⋯_ : Judgement → Judgement → Set ℓ
LG I ⋯ J = LG I → LG J


module el where

  data Origin {J B} (J⁺ : Polarisedᴶ + J) (f : LG J [ el B ]ᴶ) : Set ℓ where
   origin :  (f′  : ∀ {G} → LG G ⊢ el B ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ ax)
                   → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B} (J⁺ : Polarisedᴶ + J) (f : LG J [ el B ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       ax        = origin id refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ el B ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g f)
      go I⁺ x {J⁺} g with viewOrigin I⁺ x
      ... | origin f pr rewrite pr = origin (g ∘ f) refl



module ⊗ where

  data Origin {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⊗ C ]ᴶ) : Set ℓ where
    origin : ∀ {E F}  (h₁  : LG E ⊢ B)
              (h₂  : LG F ⊢ C)
              (f′  : ∀ {G} → LG E ⊗ F ⊢ G ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ (m⊗ h₁ h₂))
                   → Origin J⁻ f

  mutual
    viewOrigin : ∀ {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⊗ C ]ᴶ) → Origin J⁻ f
    viewOrigin (._ ⊢> [])       (m⊗  f g) = origin f g id refl
    viewOrigin (._ ⊢> [])       (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> []))       f r⇒⊗
    viewOrigin (._ ⊢> [])       (r⇐⊗ f)   = go (_ ⊢> ([] <⇐ _))       f r⇐⊗
    viewOrigin (._ ⊢> [])       (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> []))       f r⊕⇛
    viewOrigin (._ ⊢> [])       (r⊕⇚ f)   = go (_ ⊢> ([] <⊕ _))       f r⊕⇚
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B C}
         → (I⁻ : Polarisedᴶ - I) (f : LG I [ B ⊗ C ]ᴶ)
         → {J⁻ : Polarisedᴶ - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁻ (g f)
      go I⁻ f {J⁻} g with viewOrigin I⁻ f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl



module ⇒ where

  data Origin {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇒ C ]ᴶ) : Set ℓ where
    origin : ∀ {E F}  (h₁  : LG E ⊢ B)
              (h₂  : LG C ⊢ F)
              (f′  : ∀ {G} → LG G ⊢ E ⇒ F ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ (m⇒ h₁ h₂))
                   → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇒ C ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       (m⇒  f g) = origin f g id refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B C}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ B ⇒ C ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


module ⇐ where

  data Origin {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇐ C ]ᴶ) : Set ℓ where
    origin : ∀ {E F}  (h₁  : LG B ⊢ E)
              (h₂  : LG F ⊢ C)
              (f′  : ∀ {G} → LG G ⊢ E ⇐ F ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ (m⇐ h₁ h₂))
                   → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⇐ C ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       (m⇐  f g) = origin f g id refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚  g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B C}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ B ⇐ C ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


module ⊕ where

  data Origin {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⊕ C ]ᴶ) : Set ℓ where
    origin : ∀ {E F}  (h₁  : LG B ⊢ E)
              (h₂  : LG C ⊢ F)
              (f′  : ∀ {G} → LG G ⊢ E ⊕ F ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ (m⊕ h₁ h₂))
                   → Origin J⁺ f

  mutual
    viewOrigin : ∀ {J B C} (J⁺ : Polarisedᴶ + J) (f : LG J [ B ⊕ C ]ᴶ) → Origin J⁺ f
    viewOrigin ([] <⊢ ._)       (m⊕  f g) = origin f g id refl
    viewOrigin ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
    viewOrigin ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
    viewOrigin ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
    viewOrigin ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B C}
         → (I⁺ : Polarisedᴶ + I) (f : LG I [ B ⊕ C ]ᴶ)
         → {J⁺ : Polarisedᴶ + J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁺ (g f)
      go I⁺ f {J⁺} g with viewOrigin I⁺ f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


module ⇚ where

  data Origin {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇚ C ]ᴶ) : Set ℓ where
    origin : ∀ {E F}  (h₁  : LG E ⊢ B)
              (h₂  : LG C ⊢ F)
              (f′  : ∀ {G} → LG E ⇚ F ⊢ G ⋯ J [ G ]ᴶ)
              (pr  : f ≡ f′ (m⇚ h₁ h₂))
                   → Origin J⁻ f

  mutual
    viewOrigin : ∀ {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇚ C ]ᴶ) → Origin J⁻ f
    viewOrigin (._ ⊢> [])       (m⇚  f g) = origin f g id refl
    viewOrigin (._ ⊢> [])       (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> []))       f r⇒⊗
    viewOrigin (._ ⊢> [])       (r⇐⊗ f)   = go (_ ⊢> ([] <⇐ _))       f r⇐⊗
    viewOrigin (._ ⊢> [])       (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> []))       f r⊕⇛
    viewOrigin (._ ⊢> [])       (r⊕⇚ f)   = go (_ ⊢> ([] <⊕ _))       f r⊕⇚
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B C}
         → (I⁻ : Polarisedᴶ - I) (f : LG I [ B ⇚ C ]ᴶ)
         → {J⁻ : Polarisedᴶ - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁻ (g f)
      go I⁻ f {J⁻} g with viewOrigin I⁻ f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


module ⇛ where

  data Origin {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇛ C ]ᴶ) : Set ℓ where
    origin : ∀ {E F}  (h₁   : LG B ⊢ E)
              (h₂   : LG F ⊢ C)
              (f′   : ∀ {G} → LG E ⇛ F ⊢ G ⋯ J [ G ]ᴶ)
              (pr   : f ≡ f′ (m⇛ h₁ h₂))
                   → Origin J⁻ f

  mutual
    viewOrigin : ∀ {J B C} (J⁻ : Polarisedᴶ - J) (f : LG J [ B ⇛ C ]ᴶ) → Origin J⁻ f
    viewOrigin (._ ⊢> [])       (m⇛  f g) = origin f g id refl
    viewOrigin (._ ⊢> [])       (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> []))       f r⇒⊗
    viewOrigin (._ ⊢> [])       (r⇐⊗ f)   = go (_ ⊢> ([] <⇐ _))       f r⇐⊗
    viewOrigin (._ ⊢> [])       (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> []))       f r⊕⇛
    viewOrigin (._ ⊢> [])       (r⊕⇚ f)   = go (_ ⊢> ([] <⊕ _))       f r⊕⇚
    viewOrigin ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
    viewOrigin ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
    viewOrigin ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
    viewOrigin ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
    viewOrigin ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
    viewOrigin ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
    viewOrigin ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
    viewOrigin ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
    viewOrigin ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
    viewOrigin ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
    viewOrigin ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
    viewOrigin ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
    viewOrigin (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
    viewOrigin (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
    viewOrigin (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
    viewOrigin (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
    viewOrigin (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
    viewOrigin (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
    viewOrigin (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
    viewOrigin (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
    viewOrigin (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
    viewOrigin (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

    private
      go : ∀ {I J B C}
         → (I⁻ : Polarisedᴶ - I) (f : LG I [ B ⇛ C ]ᴶ)
         → {J⁻ : Polarisedᴶ - J} (g : ∀ {G} → LG I [ G ]ᴶ ⋯ J [ G ]ᴶ)
         → Origin J⁻ (g f)
      go I⁻ f {J⁻} g with viewOrigin I⁻ f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


trans′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
trans′ {B = el _ }  f  g with el.viewOrigin ([] <⊢ _) g
... | (el.origin        g′ pr)  = g′ f
trans′ {B = _ ⊗ _}  f  g with ⊗.viewOrigin (_ ⊢> []) f
... | (⊗.origin  h₁ h₂  f′ pr)  = f′ (r⇐⊗ (trans′ h₁ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ g))))))
trans′ {B = _ ⇐ _}  f  g with ⇐.viewOrigin ([] <⊢ _) g
... | (⇐.origin  h₁ h₂  g′ pr)  = g′ (r⊗⇐ (r⇒⊗ (trans′ h₂ (r⊗⇒ (trans′ (r⇐⊗ f) h₁)))))
trans′ {B = _ ⇒ _}  f  g with ⇒.viewOrigin ([] <⊢ _) g
... | (⇒.origin  h₁ h₂  g′ pr)  = g′ (r⊗⇒ (r⇐⊗ (trans′ h₁ (r⊗⇐ (trans′ (r⇒⊗ f) h₂)))))
trans′ {B = _ ⊕ _}  f  g with ⊕.viewOrigin ([] <⊢ _) g
... | (⊕.origin  h₁ h₂  g′ pr)  = g′ (r⇚⊕ (trans′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ f) h₂))) h₁))
trans′ {B = _ ⇚ _}  f  g with ⇚.viewOrigin (_ ⊢> []) f
... | (⇚.origin  h₁ h₂  f′ pr)  = f′ (r⊕⇚ (r⇛⊕ (trans′ (r⊕⇛ (trans′ h₁ (r⇚⊕ g))) h₂)))
trans′ {B = _ ⇛ _}  f  g with ⇛.viewOrigin (_ ⊢> []) f
... | (⇛.origin  h₁ h₂  f′ pr)  = f′ (r⊕⇛ (r⇚⊕ (trans′ (r⊕⇚ (trans′ h₂ (r⇛⊕ g))) h₁)))
