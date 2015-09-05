## Continuation-Passing Style
``` hidden
module continuation-passing_style where

  open import Logic.Polarity
  open import non-associative_lambek_calculus
  open import display_calculus renaming (module display_calculus to dspcal)
```

## CPS Semantics

``` hidden
module translation_to_agda (Atom : Set) (Polarityᴬ? : Atom → Polarity) (⟦_⟧ᴬ : Atom → Set) (R : Set) where
  open import Data.Product
  open import Function                   using (flip)
  open import Relation.Nullary.Decidable using (True; toWitness)
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open dspcal Atom using (Struct; ·_·; _⇐_; _⊗_; _⇒_; Sequent; _⊢_; [_]⊢_; _⊢[_])
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

```
  app₁ : ∀ {A} {{n : True (Negative?  A)}}  →  ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
  app₂ : ∀ {B} {{p : True (Positive?  B)}}  →  ⟦ B ⟧⁺ → ⟦ B ⟧⁻ → R
  app₃ : ∀ {A} {{p : True (Positive?  A)}}  → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
  app₄ : ∀ {B} {{n : True (Negative?  B)}}  → (⟦ B ⟧⁻ → R) → ⟦ B ⟧⁺
```

Given the knowledge that A is a negative and positive types,
respectively, the types for `app₁` and `app₂` unfold to `⟦ A ⟧ᵖ →
(⟦ A ⟧ᵖ → R) → R`. Likewise, given the knowledge about A in `app₃` and
`app₄`, we know that their types unfold to `(⟦ A ⟧ᵖ → R) → ⟦ A ⟧ᵖ →
R`. Both these types correspond to function application.

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
  ⟦_⟧ʲ : Sequent → Set
  ⟦   X  ⊢  Y   ⟧ʲ = ⟦ X ⟧ˢ → ⟦ Y ⟧ˢ → R
  ⟦ [ A ]⊢  Y   ⟧ʲ = ⟦ Y ⟧ˢ → ⟦ A ⟧⁻
  ⟦   X  ⊢[ B ] ⟧ʲ = ⟦ X ⟧ˢ → ⟦ B ⟧⁺
```

```
  ⟦_⟧ : ∀ {J} → fNL J → ⟦ J ⟧ʲ
  ⟦ ax⁺        ⟧ = λ x → x
  ⟦ ax⁻        ⟧ = λ x → x
  ⟦ ↼{A}  f    ⟧ = λ y x → app₁ {A} (⟦ f ⟧ x) y
  ⟦ ⇀{A}  f    ⟧ = λ x y → app₂ {A} (⟦ f ⟧ x) y
  ⟦ ↽{A}  f    ⟧ = λ y   → app₃ {A} (λ x → ⟦ f ⟧ x y)
  ⟦ ⇁{A}  f    ⟧ = λ x   → app₄ {A} (λ y → ⟦ f ⟧ x y)
  ⟦ ⊗L    f    ⟧ = ⟦ f ⟧
  ⟦ ⇒L    f g  ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
  ⟦ ⇐L    f g  ⟧ = λ{(x , y) → ⟦ g ⟧ x , ⟦ f ⟧ y}
  ⟦ ⊗R    f g  ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
  ⟦ ⇒R    f    ⟧ = ⟦ f ⟧
  ⟦ ⇐R    f    ⟧ = ⟦ f ⟧
  ⟦ r⇒⊗   f    ⟧ = λ{(x , y) z → ⟦ f ⟧ y (x , z)}
  ⟦ r⊗⇒   f    ⟧ = λ{y (x , z) → ⟦ f ⟧ (x , y) z}
  ⟦ r⇐⊗   f    ⟧ = λ{(x , y) z → ⟦ f ⟧ x (z , y)}
  ⟦ r⊗⇐   f    ⟧ = λ{x (z , y) → ⟦ f ⟧ (x , y) z}
```
