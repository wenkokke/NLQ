``` hidden
module quantifier_raising (Atom : Set) where

infixr 30 _⇒_ _⇨_
infixl 30 _⇐_ _⇦_
infixr 20 _∙_
infixr 20 _∘_
infix  3  _⊢_
```

## Quantifier Raising as structural rule


```
data Type : Set where
  el  : Atom → Type
  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type
  _⇨_ : Type → Type → Type
  _⇦_ : Type → Type → Type
```

```
data Structure : Set where
  ·_·  : Type      → Structure
  _∙_  : Structure → Structure → Structure
  _∘_  : Structure → Structure → Structure
  I    : Structure
  B    : Structure
  C    : Structure
```

```
data Judgement : Set where
  _⊢_ : Structure → Type → Judgement
```
