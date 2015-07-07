``` hidden
module lg_base (Atom : Set) where
```

## The Lambek-Grishin calculus


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
``` hidden
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



### Focusing and Polarity
``` hidden
module FocPol where

  open import Data.Product using (_×_; proj₁)
  open import Relation.Nullary.Decidable using (True)
  open import Logic.Polarity
  open import Logic.Classical.Ordered.LambekGrishin.Type           (Polarity × Atom)
  open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised (Polarity × Atom) proj₁

  infix  1  LG_
  infix  2  _⊢_
  infix  2  [_]⊢_
  infix  2  _⊢[_]
```

```
  data Struct : Polarity → Set where

    -- structures for NL

    _⊕_ : (Γ⁻ : Struct -) (Δ⁻ : Struct -) → Struct -
    _⇚_ : (Γ⁺ : Struct +) (Δ⁻ : Struct -) → Struct +
    _⇛_ : (Γ⁻ : Struct -) (Δ⁺ : Struct +) → Struct +
```
``` hidden
    ·_· : {p  : Polarity}
          (A  : Type)                     → Struct p
    _⊗_ : (Γ⁺ : Struct +) (Δ⁺ : Struct +) → Struct +
    _⇒_ : (Γ⁺ : Struct +) (Δ⁻ : Struct -) → Struct -
    _⇐_ : (Γ⁻ : Struct -) (Δ⁺ : Struct +) → Struct -
```
``` hidden
  data Judgement : Set where
    _⊢_    : Struct +  → Struct -  → Judgement
    [_]⊢_  : Type      → Struct -  → Judgement
    _⊢[_]  : Struct +  → Type      → Judgement
```
```
  data fLG_ : Judgement → Set where

    -- rules for fNL

    ⊕ᴸ   : ∀ {X Y A B} →  fLG [ B ]⊢ Y →  fLG [ A ]⊢ X →  fLG [ B ⊕ A ]⊢ Y ⊕ X
    ⊕ᴿ   : ∀ {X A B}   →  fLG X ⊢ · B · ⊕ · A · →  fLG X ⊢ · B ⊕ A ·
    ⇚ᴸ   : ∀ {X A B}   →  fLG · A · ⇚ · B · ⊢ X →  fLG · A ⇚ B · ⊢ X
    ⇚ᴿ   : ∀ {X Y A B} →  fLG X ⊢[ A ] →  fLG [ B ]⊢ Y →  fLG X ⇚ Y ⊢[ A ⇚ B ]
    ⇛ᴸ   : ∀ {X A B}   →  fLG · B · ⇛ · A · ⊢ X →  fLG · B ⇛ A · ⊢ X
    ⇛ᴿ   : ∀ {X Y A B} →  fLG X ⊢[ A ] →  fLG [ B ]⊢ Y →  fLG Y ⇛ X ⊢[ B ⇛ A ]
    r⇚⊕  : ∀ {X Y Z}   →  fLG Z ⇚ X ⊢ Y →  fLG Z ⊢ Y ⊕ X
    r⊕⇚  : ∀ {X Y Z}   →  fLG Z ⊢ Y ⊕ X →  fLG Z ⇚ X ⊢ Y
    r⇛⊕  : ∀ {X Y Z}   →  fLG Y ⇛ Z ⊢ X →  fLG Z ⊢ Y ⊕ X
    r⊕⇛  : ∀ {X Y Z}   →  fLG Z ⊢ Y ⊕ X →  fLG Y ⇛ Z ⊢ X

    d⇛⇐  : ∀ {X Y Z W} →  fLG X ⊗ Y ⊢ Z ⊕ W →  fLG Z ⇛ X ⊢ W ⇐ Y
    d⇛⇒  : ∀ {X Y Z W} →  fLG X ⊗ Y ⊢ Z ⊕ W →  fLG Z ⇛ Y ⊢ X ⇒ W
    d⇚⇒  : ∀ {X Y Z W} →  fLG X ⊗ Y ⊢ Z ⊕ W →  fLG Y ⇚ W ⊢ X ⇒ Z
    d⇚⇐  : ∀ {X Y Z W} →  fLG X ⊗ Y ⊢ Z ⊕ W →  fLG X ⇚ W ⊢ Z ⇐ Y
```
``` hidden
    ax⁺ : ∀ {A} → fLG · A · ⊢[ A ]
    ax⁻ : ∀ {A} → fLG [ A ]⊢ · A ·

    ⇁   : ∀ {X A} {p : True (Negative? A)} → fLG X ⊢ · A · → fLG X ⊢[  A  ]
    ↽   : ∀ {X A} {p : True (Positive? A)} → fLG  · A · ⊢ X → fLG [  A  ]⊢ X
    ⇀   : ∀ {X A} {p : True (Positive? A)} → fLG X ⊢[  A  ] → fLG X ⊢ · A ·
    ↼   : ∀ {X A} {p : True (Negative? A)} → fLG [  A  ]⊢ X → fLG  · A · ⊢ X

    ⊗ᴸ  : ∀ {Y A B}   →  fLG · A · ⊗ · B · ⊢ Y → fLG · A ⊗ B · ⊢ Y
    ⊗ᴿ  : ∀ {X Y A B} →  fLG X ⊢[ A ] → fLG Y ⊢[ B ] → fLG X ⊗ Y ⊢[ A ⊗ B ]
    ⇒ᴸ  : ∀ {X Y A B} →  fLG X ⊢[ A ] → fLG [ B ]⊢ Y → fLG [ A ⇒ B ]⊢ X ⇒ Y
    ⇒ᴿ  : ∀ {X A B}   →  fLG X ⊢ · A · ⇒ · B · → fLG X ⊢ · A ⇒ B ·
    ⇐ᴸ  : ∀ {X Y A B} →  fLG X ⊢[ A ] → fLG [ B ]⊢ Y → fLG [ B ⇐ A ]⊢ Y ⇐ X
    ⇐ᴿ  : ∀ {X A B}   →  fLG X ⊢ · B · ⇐ · A · → fLG X ⊢ · B ⇐ A ·
    r⇒⊗ : ∀ {X Y Z}   →  fLG Y ⊢ X ⇒ Z → fLG X ⊗ Y ⊢ Z
    r⊗⇒ : ∀ {X Y Z}   →  fLG X ⊗ Y ⊢ Z → fLG Y ⊢ X ⇒ Z
    r⇐⊗ : ∀ {X Y Z}   →  fLG X ⊢ Z ⇐ Y → fLG X ⊗ Y ⊢ Z
    r⊗⇐ : ∀ {X Y Z}   →  fLG X ⊗ Y ⊢ Z → fLG X ⊢ Z ⇐ Y
```
