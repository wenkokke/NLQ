``` hidden
module lambek_grishin_calculus (Atom : Set) where
```

# The Lambek-Grishin calculus

``` hidden
module ResMon where

  infix  1  RM_
  infix  3  _⊢_
  infixr 20 _⇒_
  infixl 20 _⇐_
  infixl 25 _⇚_
  infixr 25 _⇛_
  infixr 30 _⊗_
  infixr 30 _⊕_
```
```
  data Type : Set where

    -- types for NL

    _⊕_ : Type → Type → Type
    _⇚_ : Type → Type → Type
    _⇛_ : Type → Type → Type
```
``` hidden
    el  : Atom → Type

    _⊗_ : Type → Type → Type
    _⇒_ : Type → Type → Type
    _⇐_ : Type → Type → Type
```
```
  data Judgement : Set where
    _⊢_ : Type → Type → Judgement
```
```
  data RM_ : Judgement → Set where

    -- rules for NL

    m⊕   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM A ⊕ C ⊢ B ⊕ D
    m⇛   : ∀ {A B C D} → RM C ⊢ D     → RM A ⊢ B     → RM D ⇛ A ⊢ C ⇛ B
    m⇚   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM A ⇚ D ⊢ B ⇚ C

    r⇛⊕  : ∀ {A B C}   → RM B ⇛ C ⊢ A → RM C ⊢ B ⊕ A
    r⊕⇛  : ∀ {A B C}   → RM C ⊢ B ⊕ A → RM B ⇛ C ⊢ A
    r⊕⇚  : ∀ {A B C}   → RM C ⊢ B ⊕ A → RM C ⇚ A ⊢ B
    r⇚⊕  : ∀ {A B C}   → RM C ⇚ A ⊢ B → RM C ⊢ B ⊕ A

    d⇛⇐ : ∀ {A B C D} → RM A ⊗ B ⊢ C ⊕ D → RM C ⇛ A ⊢ D ⇐ B
    d⇛⇒ : ∀ {A B C D} → RM A ⊗ B ⊢ C ⊕ D → RM C ⇛ B ⊢ A ⇒ D
    d⇚⇒ : ∀ {A B C D} → RM A ⊗ B ⊢ C ⊕ D → RM B ⇚ D ⊢ A ⇒ C
    d⇚⇐ : ∀ {A B C D} → RM A ⊗ B ⊢ C ⊕ D → RM A ⇚ D ⊢ C ⇐ B
```
``` hidden
    ax   : ∀ {A}       → RM el A ⊢ el A
    m⊗   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM A ⊗ C ⊢ B ⊗ D
    m⇒   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM B ⇒ C ⊢ A ⇒ D
    m⇐   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM A ⇐ D ⊢ B ⇐ C
    r⇒⊗  : ∀ {A B C}   → RM B ⊢ A ⇒ C → RM A ⊗ B ⊢ C
    r⊗⇒  : ∀ {A B C}   → RM A ⊗ B ⊢ C → RM B ⊢ A ⇒ C
    r⇐⊗  : ∀ {A B C}   → RM A ⊢ C ⇐ B → RM A ⊗ B ⊢ C
    r⊗⇐  : ∀ {A B C}   → RM A ⊗ B ⊢ C → RM A ⊢ C ⇐ B
```
