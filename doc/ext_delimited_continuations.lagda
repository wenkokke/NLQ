## Syntactically Delimited Continuations
``` hidden
open import Data.Product
open import Function
open import Logic.Polarity
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality

module ext_delimited_continuations where

open import Data.Product                          using (∃; _×_; proj₁)
open import Relation.Nullary.Decidable            using (True; toWitness)

module syntactically_delimited_continuations
       (Atom : Set) (Polarityᴬ? : Atom → Polarity) (⟦_⟧ᴬ : Atom → Set) (R : Set) where

  infix 1 EXP_
  infix 2 ∈⊢-syntax ∈∶⊢-syntax ∈⊢∶-syntax
  infix 2 ∈[]⊢-syntax ∈[]⊢∶-syntax
  infix 2 ∈⊢[]-syntax ∈∶⊢[]-syntax
  infixr 30 _⊗_
  infixr 20 _⇒_
  infixl 20 _⇐_
```
```
  data Type : Set where

    -- types for fNL

    ◇_   : Type  → Type
```
``` hidden
    el   : Atom  → Type
    _⊗_  : Type  → Type → Type
    _⇒_  : Type  → Type → Type
    _⇐_  : Type  → Type → Type

  data Positive : Type → Set where
    el   : (A    : Atom)  → Polarityᴬ? A ≡ + → Positive (el A)
    ◇_   : (A    : Type)  → Positive (◇   A)
    _⊗_  : (A B  : Type)  → Positive (A ⊗ B)

  Positive? : (A : Type) → Dec (Positive A)
  Positive? (el  A) with Polarityᴬ? A | inspect Polarityᴬ? A
  ...| + | [ A⁺ ] = yes (el A A⁺)
  ...| - | [ A⁻ ] = no (λ { (el .A A⁺) → +≠- (trans (sym A⁺) A⁻) })
  Positive? (A ⊗ B) = yes (A ⊗ B)
  Positive? (◇   A) = yes (◇   A)
  Positive? (A ⇒ B) = no (λ ())
  Positive? (A ⇐ B) = no (λ ())

  data Negative : Type → Set where
    el   : (A    : Atom)  → Polarityᴬ? A ≡ - → Negative (el A)
    _⇒_  : (A B  : Type)  → Negative (A ⇒ B)
    _⇐_  : (A B  : Type)  → Negative (A ⇐ B)

  Negative? : (A : Type) → Dec (Negative A)
  Negative? (el  A) with Polarityᴬ? A | inspect Polarityᴬ? A
  ...| + | [ A⁺ ] = no (λ { (el .A A⁻) → +≠- (trans (sym A⁺) A⁻) })
  ...| - | [ A⁻ ] = yes (el A A⁻)
  Negative? (A ⊗ B) = no (λ ())
  Negative? (◇   A) = no (λ ())
  Negative? (A ⇒ B) = yes (A ⇒ B)
  Negative? (A ⇐ B) = yes (A ⇐ B)

  mutual
    ⟦_⟧⁺ : Type → Set
    ⟦ el  A  ⟧⁺ with Polarityᴬ? A
    ⟦ el  A  ⟧⁺ | + =  ⟦ A ⟧ᴬ
    ⟦ el  A  ⟧⁺ | - = (⟦ A ⟧ᴬ → R) → R
    ⟦ ◇   A  ⟧⁺ =  ⟦ A ⟧⁺
    ⟦ A ⊗ B  ⟧⁺ = (⟦ A ⟧⁺ × ⟦ B ⟧⁺)
    ⟦ A ⇒ B  ⟧⁺ = (⟦ A ⟧⁺ × ⟦ B ⟧⁻) → R
    ⟦ A ⇐ B  ⟧⁺ = (⟦ A ⟧⁻ × ⟦ B ⟧⁺) → R

    ⟦_⟧⁻ : Type → Set
    ⟦ el  A  ⟧⁻ =  ⟦ A ⟧ᴬ → R
    ⟦ ◇   A  ⟧⁻ =  ⟦ A ⟧⁺ → R
    ⟦ A ⊗ B  ⟧⁻ = (⟦ A ⟧⁺ × ⟦ B ⟧⁺) → R
    ⟦ A ⇒ B  ⟧⁻ = (⟦ A ⟧⁺ × ⟦ B ⟧⁻)
    ⟦ A ⇐ B  ⟧⁻ = (⟦ A ⟧⁻ × ⟦ B ⟧⁺)

  app₁ : ∀ {A} {{n : True (Negative? A)}} →    ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
  app₂ : ∀ {B} {{p : True (Positive? B)}} →    ⟦ B ⟧⁺ → ⟦ B ⟧⁻ → R
  app₃ : ∀ {A} {{p : True (Positive? A)}} → (  ⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
  app₄ : ∀ {B} {{n : True (Negative? B)}} → (  ⟦ B ⟧⁻ → R) → ⟦ B ⟧⁺

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
    app (◇   A)  x f           = f x
    app (A ⊗ B)  x f           = f x

  app₃ {{p}} = app (toWitness p)
    where
    app : ∀ {A} (p : Positive A) → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
    app (el A p) f x rewrite p = f x
    app (◇   A)  f x           = f x
    app (A ⊗ B)  f x           = f x

  app₄ {{n}} = app (toWitness n)
    where
    app : ∀ {A} (n : Negative A) → (⟦ A ⟧⁻ → R) → ⟦ A ⟧⁺
    app (el A p)   x rewrite p = x
    app (A ⇒ B)  f x           = f x
    app (A ⇐ B)  f x           = f x
```
```
  data Struct : Polarity → Set where

    -- structures for fNL

    ⟨_⟩  : (Γ⁺ : Struct +)                  → Struct +
```
``` hidden
    ·_·  : {p  : Polarity}
         → (A  : Type)                      → Struct p
    _⊗_  : (Γ⁺ : Struct +) (Δ⁺ : Struct +)  → Struct +
    _⇒_  : (Γ⁺ : Struct +) (Δ⁻ : Struct -)  → Struct -
    _⇐_  : (Γ⁻ : Struct -) (Δ⁺ : Struct +)  → Struct -

  ⟦_⟧ : ∀ {p} → Struct p → Set
  ⟦ ·_· { + } A ⟧ = ⟦ A ⟧⁺
  ⟦ ·_· { - } A ⟧ = ⟦ A ⟧⁻
  ⟦     ⟨ X ⟩   ⟧ = ⟦ X ⟧
  ⟦     X ⊗ Y   ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
  ⟦     X ⇒ Y   ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
  ⟦     X ⇐ Y   ⟧ = ⟦ X ⟧ × ⟦ Y ⟧

  data Judgement : Set₁ where
    _⊢_∋_    : (X : Struct +) (Y : Struct -) (f : ⟦ X ⟧ → ⟦ Y ⟧ → R) → Judgement
    [_]⊢_∋_  : (A : Type    ) (Y : Struct -) (f : ⟦ Y ⟧ → ⟦ A ⟧⁻) → Judgement
    _⊢[_]∋_  : (X : Struct +) (B : Type    ) (f : ⟦ X ⟧ → ⟦ B ⟧⁺) → Judgement

  ∈⊢-syntax    = _⊢_∋_
  ∈∶⊢-syntax   = _⊢_∋_
  ∈⊢∶-syntax   = λ X Y f → X ⊢ Y ∋ flip f
  ∈[]⊢-syntax  = [_]⊢_∋_
  ∈[]⊢∶-syntax = [_]⊢_∋_
  ∈⊢[]-syntax  = _⊢[_]∋_
  ∈∶⊢[]-syntax = _⊢[_]∋_

  syntax ∈⊢-syntax    X Y        f  = f ∈ X ⊢ Y
  syntax ∈∶⊢-syntax   X Y (λ x → f) = f ∈ x ∶ X ⊢ Y
  syntax ∈⊢∶-syntax   X Y (λ y → f) = f ∈ X ⊢ y ∶ Y
  syntax ∈[]⊢-syntax  A Y        f  = f ∈[ A ]⊢ Y
  syntax ∈[]⊢∶-syntax A Y (λ y → f) = f ∈[ A ]⊢ y ∶ Y
  syntax ∈⊢[]-syntax  X B        f  = f ∈ X ⊢[ B ]
  syntax ∈∶⊢[]-syntax X B (λ x → f) = f ∈ x ∶  X ⊢[ B ]
```
```
  data EXP_ : Judgement → Set where

    -- rules for fNL

    ◇ᴿ   : ∀ {X B f}
         →  EXP f ∈ x ∶    X    ⊢[    B ]
         →  EXP f ∈ x ∶ ⟨  X ⟩  ⊢[ ◇  B ]
```
``` hidden
    ax⁺  : ∀ {A} → EXP x ∈ x ∶ · A · ⊢[ A ]
    ax⁻  : ∀ {B} → EXP x ∈[ B ]⊢ x ∶ · B ·
    ↼    : ∀ {A Y f} {p : True (Negative? A)} →  EXP f ∈[ A ]⊢ y ∶ Y    →  EXP (app₁ {A} f) ∈ · A · ⊢  y ∶ Y
    ⇀    : ∀ {X B f} {p : True (Positive? B)} →  EXP f ∈ x ∶ X ⊢[ B ]   →  EXP (app₂ {B} f) ∈ x ∶ X ⊢ · B ·
    ↽    : ∀ {A Y f} {p : True (Positive? A)} →  EXP f ∈ · A · ⊢ y ∶ Y  →  EXP (app₃ {A} f) ∈[ A ]⊢ y ∶ Y
    ⇁    : ∀ {X B f} {p : True (Negative? B)} →  EXP f ∈ x ∶ X ⊢ · B ·  →  EXP (app₄ {B} f) ∈ x ∶ X ⊢[ B ]
    ⊗ᴸ   : ∀ {A B Y f} → EXP f ∈ · A · ⊗ · B · ⊢ Y → EXP f ∈ · A ⊗ B · ⊢ Y
    ⇒ᴸ   : ∀ {A B X Y f g} → EXP f ∈ X ⊢[ A ] → EXP g ∈[ B ]⊢ Y → EXP (map f g) ∈[ A ⇒ B ]⊢ X ⇒ Y
    ⇐ᴸ   : ∀ {B A Y X f g} → EXP f ∈ X ⊢[ A ] → EXP g ∈[ B ]⊢ Y → EXP (map g f) ∈[ B ⇐ A ]⊢ Y ⇐ X
    ⊗ᴿ   : ∀ {X Y A B f g} → EXP f ∈ X ⊢[ A ] → EXP g ∈ Y ⊢[ B ] → EXP (map f g) ∈ X ⊗ Y ⊢[ A ⊗ B ]
    ⇒ᴿ   : ∀ {X A B f} → EXP f ∈ X ⊢ · A · ⇒ · B · → EXP f ∈ X ⊢ · A ⇒ B ·
    ⇐ᴿ   : ∀ {X B A f} → EXP f ∈ X ⊢ · B · ⇐ · A · → EXP f ∈ X ⊢ · B ⇐ A ·
    r⇒⊗  : ∀ {X Y Z f} → EXP f ∈ Y ⊢ X ⇒ Z → EXP (λ {(x , y) z → f y (x , z)}) ∈ X ⊗ Y ⊢ Z
    r⊗⇒  : ∀ {Y X Z f} → EXP f ∈ X ⊗ Y ⊢ Z → EXP (λ {y (x , z) → f (x , y) z}) ∈ Y ⊢ X ⇒ Z
    r⇐⊗  : ∀ {X Y Z f} → EXP f ∈ X ⊢ Z ⇐ Y → EXP (λ {(x , y) z → f x (z , y)}) ∈ X ⊗ Y ⊢ Z
    r⊗⇐  : ∀ {X Z Y f} → EXP f ∈ X ⊗ Y ⊢ Z → EXP (λ {x (z , y) → f (x , y) z}) ∈ X ⊢ Z ⇐ Y
```

```
module example where
  open import Example.System.PolEXP

  sent : Judgement
    sent = · np · ⊗ ( · ( np ⇒ s⁻ ) ⇐ s⁻ · ⊗ ( · ( np ⇐ n ) ⊗ n · ⊗ · np ⇒ s⁻ · ) ) ⊢[ s⁻ ]
```
