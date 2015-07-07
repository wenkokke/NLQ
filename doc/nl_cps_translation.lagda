## CPS-Translation
``` hidden
open import Data.Product
open import Function                   using (flip)
open import Logic.Polarity             using (Polarity; +; -)
open import Relation.Nullary.Decidable using (True; toWitness)

module nl_cps_translation
  (Atom : Set)
  (Polarityᴬ? : Atom → Polarity)
  (⟦_⟧ᴬ : Atom → Set)
  (R : Set)
  where

  open import nl_base                  Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open import nl_display_calculus      Atom using (Struct; ·_·; _⇐_; _⊗_; _⇒_)
  open import nl_focusing_and_polarity as focpol
  open focpol.nl_focusing_and_polarity Atom Polarityᴬ?
       using (Positive?; Positive; Negative?; Negative; el; _⇐_; _⊗_; _⇒_)

```

### Translation to Linear Logic

### Typing Agda programs

``` hidden
  mutual
```
```
    ⟦_⟧⁺ : Type → Set
    ⟦ el  A  ⟧⁺ with Polarityᴬ? A
    ⟦ el  A  ⟧⁺ | +  =    ⟦ A ⟧ᴬ
    ⟦ el  A  ⟧⁺ | -  = (  ⟦ A ⟧ᴬ → R) → R
    ⟦ A ⊗ B  ⟧⁺      = (  ⟦ A ⟧⁺ × ⟦ B ⟧⁺)
    ⟦ A ⇒ B  ⟧⁺      = (  ⟦ A ⟧⁺ × ⟦ B ⟧⁻) → R
    ⟦ A ⇐ B  ⟧⁺      = (  ⟦ A ⟧⁻ × ⟦ B ⟧⁺) → R

    ⟦_⟧⁻ : Type → Set
    ⟦ el  A  ⟧⁻      =    ⟦ A ⟧ᴬ → R
    ⟦ A ⊗ B  ⟧⁻      = (  ⟦ A ⟧⁺ × ⟦ B ⟧⁺) → R
    ⟦ A ⇒ B  ⟧⁻      = (  ⟦ A ⟧⁺ × ⟦ B ⟧⁻)
    ⟦ A ⇐ B  ⟧⁻      = (  ⟦ A ⟧⁻ × ⟦ B ⟧⁺)
```

\begin{spec}
  app₁ : {{n : True (Negative?  A)}} →    ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
  app₂ : {{p : True (Positive?  A)}} →    ⟦ A ⟧⁺ → ⟦ A ⟧⁻ → R
  app₃ : {{p : True (Positive?  A)}} → (  ⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
  app₄ : {{n : True (Negative?  A)}} → (  ⟦ A ⟧⁻ → R) → ⟦ A ⟧⁺
\end{spec}

Given the knowledge that A is a negative and positive types,
respectively, the types for |app₁| and |app₂| unfold to |⟦ A ⟧ᵖ →
(⟦ A ⟧ᵖ → R) → R|. Likewise, given the knowledge about A in |app₃| and
|app₄|, we know that their types unfold to |(⟦ A ⟧ᵖ → R) → ⟦ A ⟧ᵖ →
R|. Both these types correspond to function application.

``` hidden
  app₁ : ∀ {A} {{n : True (Negative? A)}} →    ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
  app₂ : ∀ {B} {{p : True (Positive? B)}} →    ⟦ B ⟧⁺ → ⟦ B ⟧⁻ → R
  app₃ : ∀ {A} {{p : True (Positive? A)}} → (  ⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
  app₄ : ∀ {B} {{n : True (Negative? B)}} → (  ⟦ B ⟧⁻ → R) → ⟦ B ⟧⁺
```
``` hidden
  app₁ {{n}} = app (toWitness n)
    where
      app : ∀ {A} (n : Negative A) → ⟦ A ⟧⁻ → (⟦ A ⟧⁺ → R)
      app (el A p) x f rewrite p = f x
      app (A ⇒ B)  x f           = f x
      app (A ⇐ B)  x f           = f x

  app₂ {{p}} = app (toWitness p)
    where
      app : ∀ {A} (p : Positive A) → ⟦ A ⟧⁺ → (⟦ A ⟧⁻ → R)
      app (el A p) x f rewrite p = f x
      app (A ⊗ B)  x f           = f x

  app₃ {{p}} = app (toWitness p)
    where
      app : ∀ {A} (p : Positive A) → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
      app (el A p) f x rewrite p = f x
      app (A ⊗ B)  f x           = f x

  app₄ {{n}} = app (toWitness n)
    where
      app : ∀ {A} (n : Negative A) → (⟦ A ⟧⁻ → R) → ⟦ A ⟧⁺
      app (el A p)   x rewrite p = x
      app (A ⇒ B)  f x           = f x
      app (A ⇐ B)  f x           = f x
```

```
  ⟦_⟧ : ∀ {p} → Struct p → Set
  ⟦ ·_· {  p = + } A  ⟧ = ⟦ A ⟧⁺
  ⟦ ·_· {  p = - } A  ⟧ = ⟦ A ⟧⁻
  ⟦        X ⊗ Y      ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
  ⟦        X ⇒ Y      ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
  ⟦        X ⇐ Y      ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
```

\begin{spec}
data Judgement : Set₁ where
     _    ⊢    _    ∋ _ : (X : Struct +)  (Y : Struct -)  (f : ⟦ X ⟧ → ⟦ Y ⟧ → R)  → Judgement
  [  _ ]  ⊢    _    ∋ _ : (A : Type)      (Y : Struct -)  (f : ⟦ Y ⟧ → ⟦ A ⟧⁻)     → Judgement
     _    ⊢ [  _ ]  ∋ _ : (X : Struct +)  (B : Type)      (f : ⟦ X ⟧ → ⟦ B ⟧⁺)     → Judgement
\end{spec}
``` hidden
  data Judgement : Set₁ where
    _⊢_∋_   : (X : Struct +)  (Y : Struct -)  (f : ⟦ X ⟧ → ⟦ Y ⟧ → R)  → Judgement
    [_]⊢_∋_ : (A : Type)      (Y : Struct -)  (f : ⟦ Y ⟧ → ⟦ A ⟧⁻)     → Judgement
    _⊢[_]∋_ : (X : Struct +)  (B : Type)      (f : ⟦ X ⟧ → ⟦ B ⟧⁺)     → Judgement
```

``` hidden
  infix 1 fNL_
  infix 2 ∈⊢-syntax ∈∶⊢-syntax ∈⊢∶-syntax
  infix 2 ∈□⊢-syntax ∈□⊢∶-syntax
  infix 2 ∈⊢□-syntax ∈∶⊢□-syntax

  ∈⊢-syntax : (X : Struct +) (Y : Struct -) (f : ⟦ X ⟧ → ⟦ Y ⟧ → R) → Judgement
  ∈⊢-syntax = _⊢_∋_
  ∈∶⊢-syntax : (X : Struct +) (Y : Struct -) (f : ⟦ X ⟧ → ⟦ Y ⟧ → R) → Judgement
  ∈∶⊢-syntax = _⊢_∋_
  ∈⊢∶-syntax : (X : Struct +) (Y : Struct -) (f : ⟦ Y ⟧ → ⟦ X ⟧ → R) → Judgement
  ∈⊢∶-syntax X Y f = X ⊢ Y ∋ flip f
  ∈□⊢-syntax : (A : Type) (Y : Struct -) (f : ⟦ Y ⟧ → ⟦ A ⟧⁻) → Judgement
  ∈□⊢-syntax = [_]⊢_∋_
  ∈□⊢∶-syntax : (A : Type) (Y : Struct -) (f : ⟦ Y ⟧ → ⟦ A ⟧⁻) → Judgement
  ∈□⊢∶-syntax = [_]⊢_∋_
  ∈⊢□-syntax : (X : Struct +) (B : Type) (f : ⟦ X ⟧ → ⟦ B ⟧⁺) → Judgement
  ∈⊢□-syntax = _⊢[_]∋_
  ∈∶⊢□-syntax : (X : Struct +) (B : Type) (f : ⟦ X ⟧ → ⟦ B ⟧⁺) → Judgement
  ∈∶⊢□-syntax = _⊢[_]∋_
```

\begin{spec}
  syntax    X    ⊢    Y    ∋                f    = f ∈       X    ⊢       Y
  syntax    X    ⊢    Y    ∋        (λ x →  f)   = f ∈ x ∶   X    ⊢       Y
  syntax    X    ⊢    Y    ∋ (flip  (λ y →  f))  = f ∈       X    ⊢ y ∶   Y
  syntax [  A ]  ⊢    Y    ∋                f    = f ∈    [  A ]  ⊢       Y
  syntax [  A ]  ⊢    Y    ∋        (λ y →  f)   = f ∈    [  A ]  ⊢ y ∶   Y
  syntax    X    ⊢ [  B ]  ∋                f    = f ∈       X    ⊢    [  B ]
  syntax    X    ⊢ [  B ]  ∋        (λ x →  f)   = f ∈ x ∶   X    ⊢    [  B ]
\end{spec}
``` hidden
  syntax ∈⊢-syntax X Y          f  = f ∈ X ⊢ Y
  syntax ∈∶⊢-syntax X Y (λ x →  f) = f ∈ x ∶ X ⊢ Y
  syntax ∈⊢∶-syntax X Y (λ y →  f) = f ∈ X ⊢ y ∶ Y
  syntax ∈□⊢-syntax A Y         f  = f ∈[ A ]⊢ Y
  syntax ∈□⊢∶-syntax A Y (λ y → f) = f ∈[ A ]⊢ y ∶ Y
  syntax ∈⊢□-syntax X B         f  = f ∈ X ⊢[ B ]
  syntax ∈∶⊢□-syntax X B (λ x → f) = f ∈ x ∶ X ⊢[ B ]
```


```
  data fNL_ : Judgement → Set where

    ax⁺  : ∀ {A}
         →  fNL x ∈ x ∶ ·  A · ⊢[      A ]
    ax⁻  : ∀ {B}
         →  fNL x ∈[       B ]⊢ x ∶ ·  B ·

    ↼    : ∀ {A Y f} {p : True (Negative? A)}
         →  fNL f ∈[ A ]⊢ y ∶ Y    →  fNL (app₁ {A} f) ∈ · A · ⊢  y ∶ Y
    ⇀    : ∀ {X B f} {p : True (Positive? B)}
         →  fNL f ∈ x ∶ X ⊢[ B ]   →  fNL (app₂ {B} f) ∈ x ∶ X ⊢ · B ·
    ↽    : ∀ {A Y f} {p : True (Positive? A)}
         →  fNL f ∈ · A · ⊢ y ∶ Y  →  fNL (app₃ {A} f) ∈[ A ]⊢ y ∶ Y
    ⇁    : ∀ {X B f} {p : True (Negative? B)}
         →  fNL f ∈ x ∶ X ⊢ · B ·  →  fNL (app₄ {B} f) ∈ x ∶ X ⊢[ B ]

    ⊗ᴸ   : ∀ {A B Y f}
         →  fNL f ∈ · A · ⊗ · B · ⊢ Y →  fNL f ∈ · A ⊗ B · ⊢ Y
    ⇒ᴿ   : ∀ {X A B f}
         →  fNL f ∈ X ⊢ · A · ⇒ · B · →  fNL f ∈ X ⊢ · A ⇒ B ·
    ⇐ᴿ   : ∀ {X B A f}
         →  fNL f ∈ X ⊢ · B · ⇐ · A · →  fNL f ∈ X ⊢ · B ⇐ A ·

    ⊗ᴿ   : ∀ {X Y A B f g}
         →  fNL f ∈ X ⊢[ A ] →  fNL g ∈ Y ⊢[ B ] →  fNL (map f g) ∈ X ⊗ Y ⊢[ A ⊗ B ]
    ⇒ᴸ   : ∀ {A B X Y f g}
         →  fNL f ∈ X ⊢[ A ] →  fNL g ∈[ B ]⊢ Y  →  fNL (map f g) ∈[ A ⇒ B ]⊢ X ⇒ Y
    ⇐ᴸ   : ∀ {B A Y X f g}
         →  fNL f ∈ X ⊢[ A ] →  fNL g ∈[ B ]⊢ Y  →  fNL (map g f) ∈[ B ⇐ A ]⊢ Y ⇐ X

    r⇒⊗  : ∀ {X Y Z f}
         →  fNL f ∈ Y ⊢ X ⇒ Z →  fNL (λ{(x , y) z → f y (x , z)})  ∈ X ⊗ Y ⊢ Z
    r⊗⇒  : ∀ {Y X Z f}
         →  fNL f ∈ X ⊗ Y ⊢ Z →  fNL (λ{y (x , z) → f (x , y) z})  ∈ Y ⊢ X ⇒ Z
    r⇐⊗  : ∀ {X Y Z f}
         →  fNL f ∈ X ⊢ Z ⇐ Y →  fNL (λ{(x , y) z → f x (z , y)})  ∈ X ⊗ Y ⊢ Z
    r⊗⇐  : ∀ {X Z Y f}
         →  fNL f ∈ X ⊗ Y ⊢ Z →  fNL (λ{x (z , y) → f (x , y) z})  ∈ X ⊢ Z ⇐ Y
```
