module minimal where

module logic {u ℓ} (Univ : Set u) (⌈_⌉ᵁ : Univ → Set ℓ) (⊥ : Set ℓ) where


  open import Function using (id; flip; _∘_)
  open import Data.Product using (_×_; _,_)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)


  infixl  30  _⇚_
  infixr  30  _⇛_
  infixr  25  _⇒_
  infixl  25  _⇐_
  infixr  20  _⊗_
  infixr  20  _⊕_


  data Type : Set u where
    el           : Univ  → Type
    _⊗_ _⇒_ _⇐_  : Type  → Type  → Type
    _⊕_ _⇚_ _⇛_  : Type  → Type  → Type


  data Judgement : Set u where
    _⊢_  : Type → Type → Judgement


  infix 1 LG_

  data LG_ : Judgement → Set u where

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


  data Polarity : Set where + -  : Polarity

  data Context (p : Polarity) : Polarity → Set u where
    []    : Context p p
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

  data Contextᴶ (p : Polarity) : Set u where
    _<⊢_  : Context p +  → Type         → Contextᴶ p
    _⊢>_  : Type         → Context p -  → Contextᴶ p

  _[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
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

  _[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
  (A <⊢ B) [ C ]ᴶ = A [ C ] ⊢ B
  (A ⊢> B) [ C ]ᴶ = A ⊢ B [ C ]


  module el where

    data Origin {B} (J : Contextᴶ +) (f : LG J [ el B ]ᴶ) : Set u where
      origin :  (f′  : ∀ {G} → LG G ⊢ el B → LG J [ G ]ᴶ)
                (pr  : f ≡ f′ ax)
                     → Origin J f

    mutual
      find : ∀ {B} (J : Contextᴶ +) (f : LG J [ el B ]ᴶ) → Origin J f
      find ([] <⊢ ._)       ax        = origin id refl
      find ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
      find ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
      find ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
      find ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B}
          → ( I : Contextᴶ + ) (f : LG I [ el B ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I x {J} g with find I x
        ... | origin f pr rewrite pr = origin (g ∘ f) refl


  module ⊗ where

    data Origin {B C} (J : Contextᴶ -) (f : LG J [ B ⊗ C ]ᴶ) : Set u where
      origin : ∀ {E F}  (h₁  : LG E ⊢ B)
               (h₂  : LG F ⊢ C)
               (f′  : ∀ {G} → LG E ⊗ F ⊢ G → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⊗ h₁ h₂))
                    → Origin J f

    mutual
      find : ∀ {B C} (J : Contextᴶ -) (f : LG J [ B ⊗ C ]ᴶ) → Origin J f
      find (._ ⊢> [])       (m⊗  f g) = origin f g id refl
      find (._ ⊢> [])       (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> []))       f r⇒⊗
      find (._ ⊢> [])       (r⇐⊗ f)   = go (_ ⊢> ([] <⇐ _))       f r⇐⊗
      find (._ ⊢> [])       (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> []))       f r⊕⇛
      find (._ ⊢> [])       (r⊕⇚ f)   = go (_ ⊢> ([] <⊕ _))       f r⊕⇚
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ - ) (f : LG I [ B ⊗ C ]ᴶ)
          → { J : Contextᴶ - } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I f {J} g with find I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl



  module ⇒ where

    data Origin {B C} (J : Contextᴶ +) (f : LG J [ B ⇒ C ]ᴶ) : Set u where
      origin : ∀ {E F}  (h₁  : LG E ⊢ B)
               (h₂  : LG C ⊢ F)
               (f′  : ∀ {G} → LG G ⊢ E ⇒ F → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⇒ h₁ h₂))
                    → Origin J f

    mutual
      find : ∀ {B C} (J : Contextᴶ +) (f : LG J [ B ⇒ C ]ᴶ) → Origin J f
      find ([] <⊢ ._)       (m⇒  f g) = origin f g id refl
      find ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
      find ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
      find ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
      find ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ + ) (f : LG I [ B ⇒ C ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I f {J} g with find I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


  module ⇐ where

    data Origin {B C} (J : Contextᴶ +) (f : LG J [ B ⇐ C ]ᴶ) : Set u where
      origin : ∀ {E F}  (h₁  : LG B ⊢ E)
               (h₂  : LG F ⊢ C)
               (f′  : ∀ {G} → LG G ⊢ E ⇐ F → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⇐ h₁ h₂))
                    → Origin J f

    mutual
      find : ∀ {B C} (J : Contextᴶ +) (f : LG J [ B ⇐ C ]ᴶ) → Origin J f
      find ([] <⊢ ._)       (m⇐  f g) = origin f g id refl
      find ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
      find ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
      find ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
      find ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚  g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ + ) (f : LG I [ B ⇐ C ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I f {J} g with find I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


  module ⊕ where

    data Origin {B C} (J : Contextᴶ +) (f : LG J [ B ⊕ C ]ᴶ) : Set u where
      origin : ∀ {E F}  (h₁  : LG B ⊢ E)
               (h₂  : LG C ⊢ F)
               (f′  : ∀ {G} → LG G ⊢ E ⊕ F → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⊕ h₁ h₂))
                    → Origin J f

    mutual
      find : ∀ {B C} (J : Contextᴶ +) (f : LG J [ B ⊕ C ]ᴶ) → Origin J f
      find ([] <⊢ ._)       (m⊕  f g) = origin f g id refl
      find ([] <⊢ ._)       (r⊗⇒ f)   = go ((_ ⊗> []) <⊢ _)       f r⊗⇒
      find ([] <⊢ ._)       (r⊗⇐ f)   = go (([] <⊗ _) <⊢ _)       f r⊗⇐
      find ([] <⊢ ._)       (r⇛⊕ f)   = go ((_ ⇛> []) <⊢ _)       f r⇛⊕
      find ([] <⊢ ._)       (r⇚⊕ f)   = go (([] <⇚ _) <⊢ _)       f r⇚⊕
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ + ) (f : LG I [ B ⊕ C ]ᴶ)
          → { J : Contextᴶ + } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I f {J} g with find I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


  module ⇚ where

    data Origin {B C} (J : Contextᴶ -) (f : LG J [ B ⇚ C ]ᴶ) : Set u where
      origin : ∀ {E F}  (h₁  : LG E ⊢ B)
               (h₂  : LG C ⊢ F)
               (f′  : ∀ {G} → LG E ⇚ F ⊢ G → LG J [ G ]ᴶ)
               (pr  : f ≡ f′ (m⇚ h₁ h₂))
                    → Origin J f

    mutual
      find : ∀ {B C} (J : Contextᴶ -) (f : LG J [ B ⇚ C ]ᴶ) → Origin J f
      find (._ ⊢> [])       (m⇚  f g) = origin f g id refl
      find (._ ⊢> [])       (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> []))       f r⇒⊗
      find (._ ⊢> [])       (r⇐⊗ f)   = go (_ ⊢> ([] <⇐ _))       f r⇐⊗
      find (._ ⊢> [])       (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> []))       f r⊕⇛
      find (._ ⊢> [])       (r⊕⇚ f)   = go (_ ⊢> ([] <⊕ _))       f r⊕⇚
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ - ) (f : LG I [ B ⇚ C ]ᴶ)
          → { J : Contextᴶ - } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I f {J} g with find I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


  module ⇛ where

    data Origin {B C} (J : Contextᴶ -) (f : LG J [ B ⇛ C ]ᴶ) : Set u where
      origin : ∀ {E F}  (h₁   : LG B ⊢ E)
               (h₂   : LG F ⊢ C)
               (f′   : ∀ {G} → LG E ⇛ F ⊢ G → LG J [ G ]ᴶ)
               (pr   : f ≡ f′ (m⇛ h₁ h₂))
                     → Origin J f

    mutual
      find : ∀ {B C} (J : Contextᴶ -) (f : LG J [ B ⇛ C ]ᴶ) → Origin J f
      find (._ ⊢> [])       (m⇛  f g) = origin f g id refl
      find (._ ⊢> [])       (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> []))       f r⇒⊗
      find (._ ⊢> [])       (r⇐⊗ f)   = go (_ ⊢> ([] <⇐ _))       f r⇐⊗
      find (._ ⊢> [])       (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> []))       f r⊕⇛
      find (._ ⊢> [])       (r⊕⇚ f)   = go (_ ⊢> ([] <⊕ _))       f r⊕⇚
      find ((A ⊗> B) <⊢ ._) (m⊗  f g) = go (B <⊢ _)               g (m⊗ f)
      find ((A ⊗> B) <⊢ ._) (r⇒⊗ f)   = go (B <⊢ _)               f r⇒⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⊗> B)) <⊢ _) f r⊗⇒
      find ((A ⊗> B) <⊢ ._) (r⇐⊗ f)   = go (_ ⊢> (_ ⇐> B))        f r⇐⊗
      find ((A ⊗> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⊗> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⊗> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⊗> B)) <⊢ _) f r⇛⊕
      find ((A ⊗> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⊗> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇛> B)) <⊢ _) f r⊗⇒
      find ((A ⇛> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇛> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇛> B) <⊢ ._) (m⇛  f g) = go (B <⊢ _)               g (m⇛ f)
      find ((A ⇛> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇛> B)) <⊢ _) f r⇛⊕
      find ((A ⇛> B) <⊢ ._) (r⊕⇛ f)   = go (B <⊢ _)               f r⊕⇛
      find ((A ⇛> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇛> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇛> B) <⊢ ._) (d⇛⇐ f)   = go ((B <⊗ _) <⊢ _)        f d⇛⇐
      find ((A ⇛> B) <⊢ ._) (d⇛⇒ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A ⇚> B)) <⊢ _) f r⊗⇒
      find ((A ⇚> B) <⊢ ._) (r⊗⇐ f)   = go (((A ⇚> B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A ⇚> B) <⊢ ._) (m⇚  f g) = go (_ ⊢> B)               g (m⇚ f)
      find ((A ⇚> B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A ⇚> B)) <⊢ _) f r⇛⊕
      find ((A ⇚> B) <⊢ ._) (r⊕⇚ f)   = go (_ ⊢> (_ ⊕> B))        f r⊕⇚
      find ((A ⇚> B) <⊢ ._) (r⇚⊕ f)   = go (((A ⇚> B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A ⇚> B) <⊢ ._) (d⇚⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇒
      find ((A ⇚> B) <⊢ ._) (d⇚⇐ f)   = go (_ ⊢> (_ ⊕> B))        f d⇚⇐
      find ((A <⊗ B) <⊢ ._) (m⊗  f g) = go (A <⊢ _)               f (flip m⊗ g)
      find ((A <⊗ B) <⊢ ._) (r⇒⊗ f)   = go (_ ⊢> (A <⇒ _))        f r⇒⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⊗ B)) <⊢ _) f r⊗⇒
      find ((A <⊗ B) <⊢ ._) (r⇐⊗ f)   = go (A <⊢ _)               f r⇐⊗
      find ((A <⊗ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⊗ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⊗ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⊗ B)) <⊢ _) f r⇛⊕
      find ((A <⊗ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⊗ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇛ B)) <⊢ _) f r⊗⇒
      find ((A <⇛ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇛ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇛ B) <⊢ ._) (m⇛  f g) = go (_ ⊢> A)               f (flip m⇛ g)
      find ((A <⇛ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇛ B)) <⊢ _) f r⇛⊕
      find ((A <⇛ B) <⊢ ._) (r⊕⇛ f)   = go (_ ⊢> (A <⊕ _))        f r⊕⇛
      find ((A <⇛ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇛ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇛ B) <⊢ ._) (d⇛⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇐
      find ((A <⇛ B) <⊢ ._) (d⇛⇒ f)   = go (_ ⊢> (A <⊕ _))        f d⇛⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇒ f)   = go ((_ ⊗> (A <⇚ B)) <⊢ _) f r⊗⇒
      find ((A <⇚ B) <⊢ ._) (r⊗⇐ f)   = go (((A <⇚ B) <⊗ _) <⊢ _) f r⊗⇐
      find ((A <⇚ B) <⊢ ._) (m⇚  f g) = go (A <⊢ _)               f (flip m⇚ g)
      find ((A <⇚ B) <⊢ ._) (r⇛⊕ f)   = go ((_ ⇛> (A <⇚ B)) <⊢ _) f r⇛⊕
      find ((A <⇚ B) <⊢ ._) (r⊕⇚ f)   = go (A <⊢ _)               f r⊕⇚
      find ((A <⇚ B) <⊢ ._) (r⇚⊕ f)   = go (((A <⇚ B) <⇚ _) <⊢ _) f r⇚⊕
      find ((A <⇚ B) <⊢ ._) (d⇚⇒ f)   = go ((_ ⊗> A) <⊢ _)        f d⇚⇒
      find ((A <⇚ B) <⊢ ._) (d⇚⇐ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A ⊕> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⊕> B))) f r⇒⊗
      find (._ ⊢> (A ⊕> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⊕> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⊕> B)) (m⊕  f g) = go (_ ⊢> B)               g (m⊕ f)
      find (._ ⊢> (A ⊕> B)) (r⇛⊕ f)   = go (_ ⊢> B)               f r⇛⊕
      find (._ ⊢> (A ⊕> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⊕> B))) f r⊕⇛
      find (._ ⊢> (A ⊕> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⊕> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⊕> B)) (r⇚⊕ f)   = go ((_ ⇚> B) <⊢ _)        f r⇚⊕
      find (._ ⊢> (A ⇒> B)) (m⇒  f g) = go (_ ⊢> B)               g (m⇒ f)
      find (._ ⊢> (A ⇒> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇒> B))) f r⇒⊗
      find (._ ⊢> (A ⇒> B)) (r⊗⇒ f)   = go (_ ⊢> B)               f r⊗⇒
      find (._ ⊢> (A ⇒> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇒> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇒> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇒> B))) f r⊕⇛
      find (._ ⊢> (A ⇒> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇒> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇒> B)) (d⇛⇒ f)   = go (_ ⊢> (_ ⊕> B))        f d⇛⇒
      find (._ ⊢> (A ⇒> B)) (d⇚⇒ f)   = go (_ ⊢> (B <⊕ _))        f d⇚⇒
      find (._ ⊢> (A ⇐> B)) (m⇐  f g) = go (B <⊢ _)               g (m⇐ f)
      find (._ ⊢> (A ⇐> B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A ⇐> B))) f r⇒⊗
      find (._ ⊢> (A ⇐> B)) (r⇐⊗ f)   = go (_ ⊢> ((A ⇐> B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A ⇐> B)) (r⊗⇐ f)   = go ((_ ⊗> B) <⊢ _)        f r⊗⇐
      find (._ ⊢> (A ⇐> B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A ⇐> B))) f r⊕⇛
      find (._ ⊢> (A ⇐> B)) (r⊕⇚ f)   = go (_ ⊢> ((A ⇐> B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A ⇐> B)) (d⇛⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇛⇐
      find (._ ⊢> (A ⇐> B)) (d⇚⇐ f)   = go ((_ ⊗> B) <⊢ _)        f d⇚⇐
      find (._ ⊢> (A <⊕ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⊕ B))) f r⇒⊗
      find (._ ⊢> (A <⊕ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⊕ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⊕ B)) (m⊕  f g) = go (_ ⊢> A)               f (flip m⊕ g)
      find (._ ⊢> (A <⊕ B)) (r⇛⊕ f)   = go ((A <⇛ _) <⊢ _)        f r⇛⊕
      find (._ ⊢> (A <⊕ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⊕ B))) f r⊕⇛
      find (._ ⊢> (A <⊕ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⊕ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⊕ B)) (r⇚⊕ f)   = go (_ ⊢> A)               f r⇚⊕
      find (._ ⊢> (A <⇒ B)) (m⇒  f g) = go (A <⊢ _)               f (flip m⇒ g)
      find (._ ⊢> (A <⇒ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇒ B))) f r⇒⊗
      find (._ ⊢> (A <⇒ B)) (r⊗⇒ f)   = go ((A <⊗ _) <⊢ _)        f r⊗⇒
      find (._ ⊢> (A <⇒ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇒ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇒ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇒ B))) f r⊕⇛
      find (._ ⊢> (A <⇒ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇒ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇒ B)) (d⇛⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇛⇒
      find (._ ⊢> (A <⇒ B)) (d⇚⇒ f)   = go ((A <⊗ _) <⊢ _)        f d⇚⇒
      find (._ ⊢> (A <⇐ B)) (m⇐  f g) = go (_ ⊢> A)               f (flip m⇐ g)
      find (._ ⊢> (A <⇐ B)) (r⇒⊗ f)   = go (_ ⊢> (_ ⇒> (A <⇐ B))) f r⇒⊗
      find (._ ⊢> (A <⇐ B)) (r⇐⊗ f)   = go (_ ⊢> ((A <⇐ B) <⇐ _)) f r⇐⊗
      find (._ ⊢> (A <⇐ B)) (r⊗⇐ f)   = go (_ ⊢> A)               f r⊗⇐
      find (._ ⊢> (A <⇐ B)) (r⊕⇛ f)   = go (_ ⊢> (_ ⊕> (A <⇐ B))) f r⊕⇛
      find (._ ⊢> (A <⇐ B)) (r⊕⇚ f)   = go (_ ⊢> ((A <⇐ B) <⊕ _)) f r⊕⇚
      find (._ ⊢> (A <⇐ B)) (d⇛⇐ f)   = go (_ ⊢> (_ ⊕> A))        f d⇛⇐
      find (._ ⊢> (A <⇐ B)) (d⇚⇐ f)   = go (_ ⊢> (A <⊕ _))        f d⇚⇐

      private
        go : ∀ {B C}
          → ( I : Contextᴶ - ) (f : LG I [ B ⇛ C ]ᴶ)
          → { J : Contextᴶ - } (g : ∀ {G} → LG I [ G ]ᴶ → LG J [ G ]ᴶ)
          → Origin J (g f)
        go I f {J} g with find I f
        ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl


  cut′ : ∀ {A B C} (f : LG A ⊢ B) (g : LG B ⊢ C) → LG A ⊢ C
  cut′ {B = el _ }  f  g with el.find ([] <⊢ _) g
  ... | (el.origin        g′ pr)  = g′ f
  cut′ {B = _ ⊗ _}  f  g with ⊗.find (_ ⊢> []) f
  ... | (⊗.origin  h₁ h₂  f′ pr)  = f′ (r⇐⊗ (cut′ h₁ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ g))))))
  cut′ {B = _ ⇐ _}  f  g with ⇐.find ([] <⊢ _) g
  ... | (⇐.origin  h₁ h₂  g′ pr)  = g′ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁)))))
  cut′ {B = _ ⇒ _}  f  g with ⇒.find ([] <⊢ _) g
  ... | (⇒.origin  h₁ h₂  g′ pr)  = g′ (r⊗⇒ (r⇐⊗ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂)))))
  cut′ {B = _ ⊕ _}  f  g with ⊕.find ([] <⊢ _) g
  ... | (⊕.origin  h₁ h₂  g′ pr)  = g′ (r⇚⊕ (cut′ (r⊕⇚ (r⇛⊕ (cut′ (r⊕⇛ f) h₂))) h₁))
  cut′ {B = _ ⇚ _}  f  g with ⇚.find (_ ⊢> []) f
  ... | (⇚.origin  h₁ h₂  f′ pr)  = f′ (r⊕⇚ (r⇛⊕ (cut′ (r⊕⇛ (cut′ h₁ (r⇚⊕ g))) h₂)))
  cut′ {B = _ ⇛ _}  f  g with ⇛.find (_ ⊢> []) f
  ... | (⇛.origin  h₁ h₂  f′ pr)  = f′ (r⊕⇛ (r⇚⊕ (cut′ (r⊕⇚ (cut′ h₂ (r⇛⊕ g))) h₁)))


  ¬_ : Set ℓ → Set ℓ
  ¬ A = A → ⊥

  ⌈_⌉ : Type → Set ℓ
  ⌈ el  A ⌉ = ⌈ A ⌉ᵁ
  ⌈ A ⊗ B ⌉ =   (  ⌈ A ⌉ ×   ⌈ B ⌉)
  ⌈ A ⇒ B ⌉ = ¬ (  ⌈ A ⌉ × ¬ ⌈ B ⌉)
  ⌈ B ⇐ A ⌉ = ¬ (¬ ⌈ B ⌉ ×   ⌈ A ⌉)
  ⌈ B ⊕ A ⌉ = ¬ (¬ ⌈ B ⌉ × ¬ ⌈ A ⌉)
  ⌈ B ⇚ A ⌉ =   (  ⌈ B ⌉ × ¬ ⌈ A ⌉)
  ⌈ A ⇛ B ⌉ =   (¬ ⌈ A ⌉ ×   ⌈ B ⌉)

  deMorgan : {A B : Set ℓ} → (¬ ¬ A) → (¬ ¬ B) → ¬ ¬ (A × B)
  deMorgan c₁ c₂ k = c₁ (λ x → c₂ (λ y → k (x , y)))

  mutual
    ⌈_⌉ᴸ : ∀ {A B} → LG A ⊢ B → ¬ ⌈ B ⌉ → ¬ ⌈ A ⌉
    ⌈ ax       ⌉ᴸ k x  = k x
    ⌈ r⇒⊗ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (y , x)) z}
    ⌈ r⊗⇒ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ z (y , x)})
    ⌈ r⇐⊗ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (x , z)) y}
    ⌈ r⊗⇐ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ y (x , z)})
    ⌈ m⊗  f g  ⌉ᴸ k    =    λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (⌈ g ⌉ᴿ y) k}
    ⌈ m⇒  f g  ⌉ᴸ k k′ = k (λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k  (⌈ g ⌉ᴸ y)) k′})
    ⌈ m⇐  f g  ⌉ᴸ k k′ = k (λ {(x , y) → deMorgan (λ k → k  (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k′})
    ⌈ r⇛⊕ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ z (y , x)})
    ⌈ r⊕⇛ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (y , x)) z}
    ⌈ r⇚⊕ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ y (x , z)})
    ⌈ r⊕⇚ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (x , z)) y}
    ⌈ m⊕  f g  ⌉ᴸ k k′ = k (λ {(x , y) → k′ (⌈ f ⌉ᴸ x , ⌈ g ⌉ᴸ y)})
    ⌈ m⇛  f g  ⌉ᴸ k    =    λ {(x , y) → deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k}
    ⌈ m⇚  f g  ⌉ᴸ k    =    λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k}
    ⌈ d⇛⇐ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (x , z)) (y , w)})}
    ⌈ d⇛⇒ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (x , w)) (z , y)})}
    ⌈ d⇚⇒ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (w , y)) (z , x)})}
    ⌈ d⇚⇐ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (z , y)) (x , w)})}

    ⌈_⌉ᴿ : ∀ {A B} → LG A ⊢ B → ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉
    ⌈ ax       ⌉ᴿ  x      k  = k x
    ⌈ r⇒⊗ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ y (λ k → k (x , z))
    ⌈ r⊗⇒ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (y , x) z})
    ⌈ r⇐⊗ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ x (λ k → k (z , y))
    ⌈ r⊗⇐ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (x , z) y})
    ⌈ m⊗  f g  ⌉ᴿ (x , y) k  = deMorgan (⌈ f ⌉ᴿ x) (⌈ g ⌉ᴿ y) k
    ⌈ m⇒  f g  ⌉ᴿ  k′     k  = k (λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k′})
    ⌈ m⇐  f g  ⌉ᴿ  k′     k  = k (λ {(x , y) → deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k′})
    ⌈ r⇛⊕ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (y , x) z})
    ⌈ r⊕⇛ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ y (λ k → k (x , z))
    ⌈ r⊕⇚ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ x (λ k → k (z , y))
    ⌈ r⇚⊕ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (x , z) y})
    ⌈ m⊕  f g  ⌉ᴿ  k′     k  = k (λ {(x , y) → k′ (⌈ f ⌉ᴸ x , ⌈ g ⌉ᴸ y)})
    ⌈ m⇛  f g  ⌉ᴿ (x , y) k  = deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k
    ⌈ m⇚  f g  ⌉ᴿ (x , y) k  = deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k
    ⌈ d⇛⇐ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (y , w) (λ k → k (x , z))})
    ⌈ d⇛⇒ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (z , y) (λ k → k (x , w))})
    ⌈ d⇚⇒ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (z , x) (λ k → k (w , y))})
    ⌈ d⇚⇐ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (x , w) (λ k → k (z , y))})


module example where

  open import Function     using (id)
  open import Data.Bool    using (Bool; _∧_)
  open import Data.Product using (_,_)

  postulate
    Entity : Set
    forAll : (Entity → Bool) → Bool
    exists : (Entity → Bool) → Bool
    LOVES  : Entity → Entity → Bool
    PERSON : Entity → Bool
    _⊃_    : Bool → Bool → Bool

  data Univ : Set where N NP S : Univ

  ⌈_⌉ᵁ : Univ → Set
  ⌈ N  ⌉ᵁ = Entity → Bool
  ⌈ NP ⌉ᵁ = Entity
  ⌈ S  ⌉ᵁ = Bool

  open logic Univ ⌈_⌉ᵁ Bool

  everyone : ⌈ (el NP ⇐ el N) ⊗ el N ⌉
  everyone = ((λ {(g , f) → forAll (λ x → f x ⊃ g x)}) , PERSON)
  loves    : ⌈ (el NP ⇒ el S) ⇐ el NP ⌉
  loves    = λ {(k , y) → k (λ {(x , k) → k (LOVES x y)})}
  someone  : ⌈ (el NP ⇐ el N) ⊗ el N ⌉
  someone  = ((λ {(g , f) → exists (λ x → f x ∧ g x)}) , PERSON)

  EVERYONE_LOVES_SOMEONE₀
   EVERYONE_LOVES_SOMEONE₁
    EVERYONE_LOVES_SOMEONE₂
     EVERYONE_LOVES_SOMEONE₃
      EVERYONE_LOVES_SOMEONE₄
       EVERYONE_LOVES_SOMEONE₅
        EVERYONE_LOVES_SOMEONE₆
        : LG ( ( el NP ⇐ el N ) ⊗ el N ) ⊗ ( ( ( el NP ⇒ el S ) ⇐ el NP ) ⊗ ( ( el NP ⇐ el N ) ⊗ el N ) ) ⊢ el S

  everyone_loves_someone₀
   everyone_loves_someone₁
    everyone_loves_someone₂
     everyone_loves_someone₃
      everyone_loves_someone₄
       everyone_loves_someone₅
        everyone_loves_someone₆
        : Bool

  EVERYONE_LOVES_SOMEONE₀
    = r⇒⊗ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ ax′) ax) (r⇐⊗ ax′)))
  everyone_loves_someone₀
    = ⌈ EVERYONE_LOVES_SOMEONE₀ ⌉ᴿ (everyone , loves , someone) id
  --> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ LOVES x y))

  EVERYONE_LOVES_SOMEONE₁
    = r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ (m⇐ ax′ (r⇐⊗ ax′))))) ax))
  everyone_loves_someone₁
    = ⌈ EVERYONE_LOVES_SOMEONE₁ ⌉ᴿ (everyone , loves , someone) id
  --> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ LOVES x y))

  EVERYONE_LOVES_SOMEONE₂
    = r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (m⇒ (r⇐⊗ ax′) ax) ax))) ax)))
  everyone_loves_someone₂
    = ⌈ EVERYONE_LOVES_SOMEONE₂ ⌉ᴿ (everyone , loves , someone) id
  --> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ LOVES x y))

  EVERYONE_LOVES_SOMEONE₃
    = r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ ax′)) ax))))) ax))
  everyone_loves_someone₃
    = ⌈ EVERYONE_LOVES_SOMEONE₃ ⌉ᴿ (everyone , loves , someone) id
  --> forAll (λ x → PERSON x ⊃ exists (λ y → PERSON y ∧ LOVES x y))

  EVERYONE_LOVES_SOMEONE₄
    = r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ ax′)) ax)))) (r⇐⊗ ax′)))
  everyone_loves_someone₄
    = ⌈ EVERYONE_LOVES_SOMEONE₄ ⌉ᴿ (everyone , loves , someone) id
  --> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ LOVES x y))

  EVERYONE_LOVES_SOMEONE₅
    = r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (m⇐ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ ax′)) ax)))) ax))) ax)))
  everyone_loves_someone₅
    = ⌈ EVERYONE_LOVES_SOMEONE₅ ⌉ᴿ (everyone , loves , someone) id
  --> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ LOVES x y))

  EVERYONE_LOVES_SOMEONE₆
    = r⇒⊗ (r⇒⊗ (r⇐⊗ (m⇐ (r⊗⇒ (r⊗⇒ (r⇐⊗ (r⇐⊗ (m⇐ (r⊗⇐ (r⇒⊗ (r⇐⊗ ax′))) ax))))) ax)))
  everyone_loves_someone₆
    = ⌈ EVERYONE_LOVES_SOMEONE₆ ⌉ᴿ (everyone , loves , someone) id
  --> exists (λ y → PERSON y ∧ forAll (λ x → PERSON x ⊃ LOVES x y))
