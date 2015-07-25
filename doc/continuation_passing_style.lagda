## Continuation-Passing Style
``` hidden
module continuation_passing_style where
  open import Logic.Polarity
  open import non_associative_lambek_calculus
  open import display_calculus
```

## CPS Semantics

### Translation to Agda
``` hidden
module translation_to_agda (Atom : Set) (Polarityᴬ? : Atom → Polarity) (⟦_⟧ᴬ : Atom → Set) (R : Set) where
  open import Data.Product
  open import Function                   using (flip)
  open import Relation.Nullary.Decidable using (True; toWitness)
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open display_calculus.display_calculus Atom using (Struct; ·_·; _⇐_; _⊗_; _⇒_; Judgement; _⊢_; [_]⊢_; _⊢[_])
  open focpol Atom Polarityᴬ?

```
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
  app₁ : ∀ {A} {{n : True (Negative? A)}} →  ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
  app₂ : ∀ {B} {{p : True (Positive? B)}} →  ⟦ B ⟧⁺ → ⟦ B ⟧⁻ → R
  app₃ : ∀ {A} {{p : True (Positive? A)}} → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
  app₄ : ∀ {B} {{n : True (Negative? B)}} → (⟦ B ⟧⁻ → R) → ⟦ B ⟧⁺
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
  ⟦_⟧ˢ : ∀ {p} → Struct p → Set
  ⟦ ·_· {  p = + } A  ⟧ˢ = ⟦ A ⟧⁺
  ⟦ ·_· {  p = - } A  ⟧ˢ = ⟦ A ⟧⁻
  ⟦        X ⊗ Y      ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
  ⟦        X ⇒ Y      ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
  ⟦        X ⇐ Y      ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
```

```
  ⟦_⟧ᴶ : Judgement → Set
  ⟦   X  ⊢  Y   ⟧ᴶ = ⟦ X ⟧ˢ → ⟦ Y ⟧ˢ → R
  ⟦ [ A ]⊢  Y   ⟧ᴶ = ⟦ Y ⟧ˢ → ⟦ A ⟧⁻
  ⟦   X  ⊢[ B ] ⟧ᴶ = ⟦ X ⟧ˢ → ⟦ B ⟧⁺
```

```
  ⟦_⟧ : ∀ {J} → fNL J → ⟦ J ⟧ᴶ
  ⟦ ax⁺        ⟧ = λ x → x
  ⟦ ax⁻        ⟧ = λ x → x
  ⟦ ↼{A}  f    ⟧ = λ y x → app₁ {A} (⟦ f ⟧ x) y
  ⟦ ⇀{A}  f    ⟧ = λ x y → app₂ {A} (⟦ f ⟧ x) y
  ⟦ ↽{A}  f    ⟧ = λ y   → app₃ {A} (λ x → ⟦ f ⟧ x y)
  ⟦ ⇁{A}  f    ⟧ = λ x   → app₄ {A} (λ y → ⟦ f ⟧ x y)
  ⟦ ⊗ᴸ    f    ⟧ = ⟦ f ⟧
  ⟦ ⇒ᴸ    f g  ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
  ⟦ ⇐ᴸ    f g  ⟧ = λ{(x , y) → ⟦ g ⟧ x , ⟦ f ⟧ y}
  ⟦ ⊗ᴿ    f g  ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
  ⟦ ⇒ᴿ    f    ⟧ = ⟦ f ⟧
  ⟦ ⇐ᴿ    f    ⟧ = ⟦ f ⟧
  ⟦ r⇒⊗   f    ⟧ = λ{(x , y) z → ⟦ f ⟧ y (x , z)}
  ⟦ r⊗⇒   f    ⟧ = λ{y (x , z) → ⟦ f ⟧ (x , y) z}
  ⟦ r⇐⊗   f    ⟧ = λ{(x , y) z → ⟦ f ⟧ x (z , y)}
  ⟦ r⊗⇐   f    ⟧ = λ{x (z , y) → ⟦ f ⟧ (x , y) z}
```


### Typing Agda programs
``` hidden
module typing_agda (Atom : Set) (Polarityᴬ? : Atom → Polarity) (⟦_⟧ᴬ : Atom → Set) (R : Set) where
  open import Data.Product
  open import Function                   using (flip)
  open import Relation.Nullary.Decidable using (True; toWitness)
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open display_calculus.display_calculus Atom using (Struct; ·_·; _⇐_; _⊗_; _⇒_; Judgement; _⊢_; [_]⊢_; _⊢[_])
  open focpol Atom using (Positive?; Negative?)
  open translation_to_agda Atom Polarityᴬ?

  mutual
    infix 2 fNL-syntax₁ fNL-syntax₂ fNL-syntax₃
            fNL-syntax₄ fNL-syntax₅ fNL-syntax₆ fNL-syntax₇

    fNL-syntax₁ = λ X Y f → fNL_ (  X  ⊢  Y  )       f
    fNL-syntax₂ = λ X Y f → fNL_ (  X  ⊢  Y  )       f
    fNL-syntax₃ = λ X Y f → fNL_ (  X  ⊢  Y  ) (flip f)
    fNL-syntax₄ = λ A Y f → fNL_ ([ A ]⊢  Y  )       f
    fNL-syntax₅ = λ A Y f → fNL_ ([ A ]⊢  Y  )       f
    fNL-syntax₆ = λ X B f → fNL_ (  X  ⊢[ B ])       f
    fNL-syntax₇ = λ X B f → fNL_ (  X  ⊢[ B ])       f
```
```
    syntax fNL-syntax₁  X  Y         f   = f ∈      X  ⊢      Y
    syntax fNL-syntax₂  X  Y (λ x →  f)  = f ∈ x ∶  X  ⊢      Y
    syntax fNL-syntax₃  X  Y (λ y →  f)  = f ∈      X  ⊢ y ∶  Y
    syntax fNL-syntax₄  A  Y         f   = f ∈[     A ]⊢      Y
    syntax fNL-syntax₅  A  Y (λ y →  f)  = f ∈[     A ]⊢ y ∶  Y
    syntax fNL-syntax₆  X  B         f   = f ∈      X  ⊢[     B ]
    syntax fNL-syntax₇  X  B (λ x →  f)  = f ∈ x ∶  X  ⊢[     B ]
```


```
    data fNL_ : (J : Judgement) (f : ⟦ J ⟧ᴶ) → Set₁ where

      ax⁺  : ∀ {A} → x ∈ x ∶ · A · ⊢[ A ]
      ax⁻  : ∀ {B} → x ∈[ B ]⊢ x ∶ · B ·

      ↼    : ∀ {A Y f} {p : True (Negative? A)}
           → f ∈[ A ]⊢ y ∶ Y    → (app₁ {A} f) ∈ · A · ⊢  y ∶ Y
      ⇀    : ∀ {X B f} {p : True (Positive? B)}
           → f ∈ x ∶ X ⊢[ B ]   → (app₂ {B} f) ∈ x ∶ X ⊢ · B ·
      ↽    : ∀ {A Y f} {p : True (Positive? A)}
           → f ∈ · A · ⊢ y ∶ Y  → (app₃ {A} f) ∈[ A ]⊢ y ∶ Y
      ⇁    : ∀ {X B f} {p : True (Negative? B)}
           → f ∈ x ∶ X ⊢ · B ·  → (app₄ {B} f) ∈ x ∶ X ⊢[ B ]

      ⊗ᴸ   : ∀ {A B Y f}
           → f ∈ · A · ⊗ · B · ⊢ Y → f ∈ · A ⊗ B · ⊢ Y
      ⇒ᴸ   : ∀ {A B X Y f g}
           → f ∈ X ⊢[ A ] → g ∈[ B ]⊢ Y → (map f g) ∈[ A ⇒ B ]⊢ X ⇒ Y
      ⇐ᴸ   : ∀ {B A Y X f g}
           → f ∈ X ⊢[ A ] → g ∈[ B ]⊢ Y → (map g f) ∈[ B ⇐ A ]⊢ Y ⇐ X

      ⊗ᴿ   : ∀ {X Y A B f g}
           → f ∈ X ⊢[ A ] → g ∈ Y ⊢[ B ] → (map f g) ∈ X ⊗ Y ⊢[ A ⊗ B ]
      ⇒ᴿ   : ∀ {X A B f}
           → f ∈ X ⊢ · A · ⇒ · B · → f ∈ X ⊢ · A ⇒ B ·
      ⇐ᴿ   : ∀ {X B A f}
           → f ∈ X ⊢ · B · ⇐ · A · → f ∈ X ⊢ · B ⇐ A ·

      r⇒⊗  : ∀ {X Y Z f}
           → f ∈ Y ⊢ X ⇒ Z → (λ{(x , y) z → f y (x , z)}) ∈ X ⊗ Y ⊢ Z
      r⊗⇒  : ∀ {Y X Z f}
           → f ∈ X ⊗ Y ⊢ Z → (λ{y (x , z) → f (x , y) z}) ∈ Y ⊢ X ⇒ Z
      r⇐⊗  : ∀ {X Y Z f}
           → f ∈ X ⊢ Z ⇐ Y → (λ{(x , y) z → f x (z , y)}) ∈ X ⊗ Y ⊢ Z
      r⊗⇐  : ∀ {X Z Y f}
           → f ∈ X ⊗ Y ⊢ Z → (λ{x (z , y) → f (x , y) z}) ∈ X ⊢ Z ⇐ Y
```
