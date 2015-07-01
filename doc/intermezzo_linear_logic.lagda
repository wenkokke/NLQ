``` hidden
open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)

module intermezzo_linear_logic (Atom : Set) where

infix  1 ILL_
infix  2 _⊢_
infixr 30 _⊗_
infixr 20 _⊸_
```

# Intermezzo: Linear Logic

In this section we shall discuss intuitionistic linear logic. The
reasons that we use intuitionistic (as opposed to classical) linear
logic, is that it has a direct translation to the lambda calculus.


```
data Type : Set where
  el   : Atom  → Type
  _⊗_  : Type  → Type → Type
  _⊸_  : Type  → Type → Type
```


```
data Judgement : Set where
  _⊢_ : List Type → Type → Judgement
```


```
data ILL_ : Judgement → Set where

  ax  : ∀ {A}
      → ILL A , ∅ ⊢ A

  ⊸ᵢ  : ∀ {Γ₁ A B}
      → ILL A , Γ₁ ⊢ B →  ILL Γ₁  ⊢ A ⊸ B

  ⊸ₑ  : ∀ {Γ₁ Γ₂ A B}
      → ILL Γ₁ ⊢ A ⊸ B →  ILL Γ₂  ⊢ A → ILL Γ₁ ++  Γ₂  ⊢ B

  ⊗ᵢ  : ∀ {Γ₁ Γ₂ A B}
      → ILL Γ₁ ⊢ A →  ILL Γ₂ ⊢ B → ILL Γ₁ ++  Γ₂ ⊢ A ⊗ B

  ⊗ₑ  : ∀ {Γ₁ Γ₂ A B C}
      → ILL Γ₁ ⊢ A ⊗ B → ILL A , B , Γ₂ ⊢ C → ILL Γ₁ ++  Γ₂ ⊢ C

  e   : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ A}
      → ILL (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A →  ILL (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A
```

```
e₁  : ∀ {A B C Γ}
    → ILL B , A , Γ ⊢ C → ILL A , B , Γ ⊢ C
e₁  = e {∅} {_ , ∅} {_ , ∅}
```
