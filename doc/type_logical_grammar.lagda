``` hidden
module type_logical_grammar (Atom : Set) (Word : Set) where
```

``` hidden
open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
```

# Type-Logical Grammar


## What is a type-logical grammar?


### Abstract categorial grammars

@degroote2001

``` hidden
module LinearImplicativeType (Atom : Set) where

  infixr 5 _⊸_
```

```
  data Type : Set where
    el   : Atom  → Type
    _⊸_  : Type  → Type → Type
```

``` hidden
  module AbstractCategorialGrammar (Word : Set) (τ : Word → Type) where

    infix  3 _⊢_
```

```
    data _⊢_ : (Γ : List Type) (α : Type) → Set where

      con : ∀ {c}        →  ∅  ⊢ τ(c)

      var : ∀ {α}        →  α , ∅  ⊢ α

      abs : ∀ {Γ α β}    →  α , Γ ⊢ β → Γ ⊢ α ⊸ β

      app : ∀ {Γ Δ α β}  →  Γ  ⊢ α ⊸ β → Δ ⊢ α → Γ ++ Δ ⊢ β
```



## What are substuctural logics?




- name type-logical grammar goes back to @morrill1994;

- goes back to two papers written by Lambek [-@lambek1958; -@lambek1961];
