``` hidden
open import Function     using (case_of_)
open import Data.List    using (List; map; _++_) renaming (_∷_ to _,_; [] to ∅)
open import Data.Product using (_×_) renaming (_,_ to _，_; uncurry′ to uncurry)

module ll_base (Atom : Set) (⟦_⟧ᴬ : Atom → Set) where

infix  1 ILL_
infix  2 _⊢_
infixr 30 _⊗_
infixr 20 _⊸_
```

## Intermezzo: Linear Logic

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

  ⊸ᵢ  : ∀ {Γ A B}
      → ILL A , Γ ⊢ B →  ILL Γ  ⊢ A ⊸ B

  ⊸ₑ  : ∀ {Γ₁ Γ₂ A B}
      → ILL Γ₁ ⊢ A ⊸ B →  ILL Γ₂  ⊢ A → ILL Γ₁ ++  Γ₂  ⊢ B

  ⊗ᵢ  : ∀ {Γ₁ Γ₂ A B}
      → ILL Γ₁ ⊢ A →  ILL Γ₂ ⊢ B → ILL Γ₁ ++  Γ₂ ⊢ A ⊗ B

  ⊗ₑ  : ∀ {Γ₁ Γ₂ A B C}
      → ILL Γ₁ ⊢ A ⊗ B → ILL A , B , Γ₂ ⊢ C → ILL Γ₁ ++  Γ₂ ⊢ C

  ex  : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ A}
      → ILL (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A →  ILL (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A
```

```
ex₁  : ∀ {A B C Γ}
     → ILL B , A , Γ ⊢ C → ILL A , B , Γ ⊢ C
ex₁  = ex {Γ₁ = ∅} {Γ₂ = _ , ∅} {Γ₃ = _ , ∅}
```



### Translation to Agda

```
data Env : List Set → Set₁ where
  ∅    : Env ∅
  _,_  : ∀ {A Γ} → A → Env Γ → Env (A , Γ)
```

``` hidden
module _ {A : Set} {f : A → Set} where
```

```
  exch  : ∀ Γ₁ Γ₂ Γ₃ Γ₄
            → Env (map f ((Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄)))
            → Env (map f ((Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄)))
  exch (_ ,  Γ₁)  Γ₂       Γ₃   Γ₄ (x ,  env)  = x , exch Γ₁ Γ₂ Γ₃ Γ₄ env
  exch       ∅    Γ₂       ∅    Γ₄       env   = env
  exch       ∅    Γ₂ (_ ,  Γ₃)  Γ₄ (x ,  env)  = ins Γ₂ (Γ₃ ++ Γ₄) x (exch ∅ Γ₂ Γ₃ Γ₄ env)
```
``` hidden
    where
```
```
      ins  : ∀ {x} → (Γ₁ Γ₂ : List A) → f x
           → Env (map f (Γ₁ ++       Γ₂))
           → Env (map f (Γ₁ ++ (x ,  Γ₂)))
      ins       ∅    Γ₂ x       env   = x , env
      ins (_ ,  Γ₁)  Γ₂ x (y ,  env)  = y , ins Γ₁ Γ₂ x env
```

```
  split : ∀ {Γ₁ Γ₂} → Env (map f (Γ₁ ++ Γ₂)) → Env (map f Γ₁) × Env (map f Γ₂)
  split {∅}      {Γ₂}       env   = (∅ ， env)
  split {_ , Γ₁} {Γ₂} (x ,  env)  with split {Γ₁} {Γ₂} env
  split {_ , Γ₁} {Γ₂} (x ,  env)  | (e₁ ， e₂) = ((x , e₁) ， e₂)
```

```
  split_as_  : ∀ {r : Set} {Γ₁ Γ₂}
               → Env (map f (Γ₁ ++ Γ₂)) → (Env (map f Γ₁) → Env (map f Γ₂) → r) → r
  split_as_ env f = uncurry f (split env)
```

```
⟦_⟧ : Type → Set
⟦ el   A  ⟧ = ⟦ A ⟧ᴬ
⟦ A ⊸  B  ⟧ = ⟦ A ⟧ →  ⟦ B ⟧
⟦ A ⊗  B  ⟧ = ⟦ A ⟧ ×  ⟦ B ⟧
```

```
⟦_⟧ˢ = map ⟦_⟧
```

```
[_] : ∀ {Γ B} → ILL Γ ⊢ B → Env ⟦ Γ ⟧ˢ → ⟦ B ⟧
[ ax       ] (  x , ∅)  = x
[ ⊸ᵢ  f    ]    env     = λ x → [ f ] (x , env)
[ ⊸ₑ  f g  ]    env     = split env as λ e₁ e₂ → [ f ] e₁  ([ g ] e₂)
[ ⊗ᵢ  f g  ]    env     = split env as λ e₁ e₂ → [ f ] e₁ ， [ g ] e₂
[ ⊗ₑ  f g  ]    env     = split env as λ e₁ e₂ → case [ f ] e₁ of (λ{(x ， y) → [ g ] (x , (y , e₂))})
[ ex {Γ₁}{Γ₂}{Γ₃}{Γ₄}  f    ]    env     = [ f ] (exch Γ₁ Γ₃ Γ₂ Γ₄ env)
```
