``` hidden
module lambek-grishin_calculus (Atom : Set) where
```

## The Lambek-Grishin calculus


``` hidden
module ResMon where


  infix  1  RM_
  infix  3  _⊢RM_
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
``` hidden
  mutual
    _⊢RM_ : Type → Type → Set
    A ⊢RM B = RM A ⊢ B
```
``` hidden
    data RM_ : Judgement → Set where

      -- rules for NL

      m⊕   : ∀ {A B C D} → A ⊢RM B     → C ⊢RM D     → A ⊕ C ⊢RM B ⊕ D
      m⇛   : ∀ {A B C D} → C ⊢RM D     → A ⊢RM B     → D ⇛ A ⊢RM C ⇛ B
      m⇚   : ∀ {A B C D} → A ⊢RM B     → C ⊢RM D     → A ⇚ D ⊢RM B ⇚ C

      r⇛⊕  : ∀ {A B C}   → B ⇛ C ⊢RM A → C ⊢RM B ⊕ A
      r⊕⇛  : ∀ {A B C}   → C ⊢RM B ⊕ A → B ⇛ C ⊢RM A
      r⊕⇚  : ∀ {A B C}   → C ⊢RM B ⊕ A → C ⇚ A ⊢RM B
      r⇚⊕  : ∀ {A B C}   → C ⇚ A ⊢RM B → C ⊢RM B ⊕ A

      d⇛⇐ : ∀ {A B C D} → A ⊗ B ⊢RM C ⊕ D → C ⇛ A ⊢RM D ⇐ B
      d⇛⇒ : ∀ {A B C D} → A ⊗ B ⊢RM C ⊕ D → C ⇛ B ⊢RM A ⇒ D
      d⇚⇒ : ∀ {A B C D} → A ⊗ B ⊢RM C ⊕ D → B ⇚ D ⊢RM A ⇒ C
      d⇚⇐ : ∀ {A B C D} → A ⊗ B ⊢RM C ⊕ D → A ⇚ D ⊢RM C ⇐ B
```
``` hidden
      ax   : ∀ {A}       → el A ⊢RM el A
      m⊗   : ∀ {A B C D} → A ⊢RM B     → C ⊢RM D     → A ⊗ C ⊢RM B ⊗ D
      m⇒   : ∀ {A B C D} → A ⊢RM B     → C ⊢RM D     → B ⇒ C ⊢RM A ⇒ D
      m⇐   : ∀ {A B C D} → A ⊢RM B     → C ⊢RM D     → A ⇐ D ⊢RM B ⇐ C
      r⇒⊗  : ∀ {A B C}   → B ⊢RM A ⇒ C → A ⊗ B ⊢RM C
      r⊗⇒  : ∀ {A B C}   → A ⊗ B ⊢RM C → B ⊢RM A ⇒ C
      r⇐⊗  : ∀ {A B C}   → A ⊢RM C ⇐ B → A ⊗ B ⊢RM C
      r⊗⇐  : ∀ {A B C}   → A ⊗ B ⊢RM C → A ⊢RM C ⇐ B
```

[compute](Example/System/LG/ResMon.agda "asMathPar (quote LG_)")


### Focusing and Polarity
``` hidden
module FocPol where

  open import Data.Product using (_×_; proj₁)
  open import Relation.Nullary.Decidable using (True)
  open import Logic.Polarity
  open import Logic.LG.Type           (Polarity × Atom)
  open import Logic.LG.Type.Polarised (Polarity × Atom) proj₁

  infix 1 fLG_
  infix 2 _⊢fLG_ [_]⊢fLG_ _⊢fLG[_]
  infix 2 _⊢_ [_]⊢_ _⊢[_]
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
``` hidden
  mutual
    _⊢fLG_ : Struct + → Struct - → Set
    X ⊢fLG Y = fLG X ⊢ Y
    _⊢fLG[_] : Struct + → Type → Set
    X ⊢fLG[ B ] = fLG X ⊢[ B ]
    [_]⊢fLG_ : Type → Struct - → Set
    [ A ]⊢fLG Y = fLG [ A ]⊢ Y
```
``` hidden
    data fLG_ : Judgement → Set where

      -- rules for fNL

      ⊕ᴸ   : ∀ {X Y A B} →  [ B ]⊢fLG Y →  [ A ]⊢fLG X →  [ B ⊕ A ]⊢fLG Y ⊕ X
      ⊕ᴿ   : ∀ {X A B}   →  X ⊢fLG · B · ⊕ · A · →  X ⊢fLG · B ⊕ A ·
      ⇚ᴸ   : ∀ {X A B}   →  · A · ⇚ · B · ⊢fLG X →  · A ⇚ B · ⊢fLG X
      ⇚ᴿ   : ∀ {X Y A B} →  X ⊢fLG[ A ] →  [ B ]⊢fLG Y →  X ⇚ Y ⊢fLG[ A ⇚ B ]
      ⇛ᴸ   : ∀ {X A B}   →  · B · ⇛ · A · ⊢fLG X →  · B ⇛ A · ⊢fLG X
      ⇛ᴿ   : ∀ {X Y A B} →  X ⊢fLG[ A ] →  [ B ]⊢fLG Y →  Y ⇛ X ⊢fLG[ B ⇛ A ]
      r⇚⊕  : ∀ {X Y Z}   →  Z ⇚ X ⊢fLG Y →  Z ⊢fLG Y ⊕ X
      r⊕⇚  : ∀ {X Y Z}   →  Z ⊢fLG Y ⊕ X →  Z ⇚ X ⊢fLG Y
      r⇛⊕  : ∀ {X Y Z}   →  Y ⇛ Z ⊢fLG X →  Z ⊢fLG Y ⊕ X
      r⊕⇛  : ∀ {X Y Z}   →  Z ⊢fLG Y ⊕ X →  Y ⇛ Z ⊢fLG X

      d⇛⇐  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  Z ⇛ X ⊢fLG W ⇐ Y
      d⇛⇒  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  Z ⇛ Y ⊢fLG X ⇒ W
      d⇚⇒  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  Y ⇚ W ⊢fLG X ⇒ Z
      d⇚⇐  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  X ⇚ W ⊢fLG Z ⇐ Y
```
``` hidden
      ax⁺ : ∀ {A} → · A · ⊢fLG[ A ]
      ax⁻ : ∀ {A} → [ A ]⊢fLG · A ·
      ⇁   : ∀ {X A} {p : True (Negative? A)} → X ⊢fLG · A · → X ⊢fLG[  A  ]
      ↽   : ∀ {X A} {p : True (Positive? A)} →  · A · ⊢fLG X → [  A  ]⊢fLG X
      ⇀   : ∀ {X A} {p : True (Positive? A)} → X ⊢fLG[  A  ] → X ⊢fLG · A ·
      ↼   : ∀ {X A} {p : True (Negative? A)} → [  A  ]⊢fLG X →  · A · ⊢fLG X
      ⊗ᴸ  : ∀ {Y A B}   →  · A · ⊗ · B · ⊢fLG Y → · A ⊗ B · ⊢fLG Y
      ⊗ᴿ  : ∀ {X Y A B} →  X ⊢fLG[ A ] → Y ⊢fLG[ B ] → X ⊗ Y ⊢fLG[ A ⊗ B ]
      ⇒ᴸ  : ∀ {X Y A B} →  X ⊢fLG[ A ] → [ B ]⊢fLG Y → [ A ⇒ B ]⊢fLG X ⇒ Y
      ⇒ᴿ  : ∀ {X A B}   →  X ⊢fLG · A · ⇒ · B · → X ⊢fLG · A ⇒ B ·
      ⇐ᴸ  : ∀ {X Y A B} →  X ⊢fLG[ A ] → [ B ]⊢fLG Y → [ B ⇐ A ]⊢fLG Y ⇐ X
      ⇐ᴿ  : ∀ {X A B}   →  X ⊢fLG · B · ⇐ · A · → X ⊢fLG · B ⇐ A ·
      r⇒⊗ : ∀ {X Y Z}   →  Y ⊢fLG X ⇒ Z → X ⊗ Y ⊢fLG Z
      r⊗⇒ : ∀ {X Y Z}   →  X ⊗ Y ⊢fLG Z → Y ⊢fLG X ⇒ Z
      r⇐⊗ : ∀ {X Y Z}   →  X ⊢fLG Z ⇐ Y → X ⊗ Y ⊢fLG Z
      r⊗⇐ : ∀ {X Y Z}   →  X ⊗ Y ⊢fLG Z → X ⊢fLG Z ⇐ Y
```


[compute](Example/System/LG/Pol.agda "asMathPar (quote fLG_)")
