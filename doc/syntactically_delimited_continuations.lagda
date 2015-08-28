## Syntactically Delimited Continuations
``` hidden
open import Data.Product
open import Function using (id; flip)
open import Logic.Polarity
open import Relation.Nullary
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; inspect; trans; sym)

module syntactically_delimited_continuations where

open import Data.Product                          using (∃; _×_; proj₁)
open import Relation.Nullary.Decidable            using (True; toWitness)

module syntactically_delimited_continuations
       (Atom : Set) (Polarityᴬ? : Atom → Polarity) (⟦_⟧ᴬ : Atom → Set) (R : Set) where

  infix 1 NL◇_
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
  ...| + | P.[ A⁺ ] = yes (el A A⁺)
  ...| - | P.[ A⁻ ] = no (λ { (el .A A⁺) → +≠- (trans (sym A⁺) A⁻) })
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
  ...| + | P.[ A⁺ ] = no (λ { (el .A A⁻) → +≠- (trans (sym A⁺) A⁻) })
  ...| - | P.[ A⁻ ] = yes (el A A⁻)
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

  mutual
    ∈⊢-syntax    = λ X Y f → NL◇ (X ⊢ Y ∋ f)
    ∈∶⊢-syntax   = λ X Y f → NL◇ (X ⊢ Y ∋ f)
    ∈⊢∶-syntax   = λ X Y f → NL◇ (X ⊢ Y ∋ flip f)
    ∈[]⊢-syntax  = λ A Y f → NL◇ ([ A ]⊢ Y ∋ f)
    ∈[]⊢∶-syntax = λ A Y f → NL◇ ([ A ]⊢ Y ∋ f)
    ∈⊢[]-syntax  = λ X B f → NL◇ (X ⊢[ B ]∋ f)
    ∈∶⊢[]-syntax = λ X B f → NL◇ (X ⊢[ B ]∋ f)

    syntax ∈⊢-syntax    X Y        f  = f ∈ X ⊢ Y
    syntax ∈∶⊢-syntax   X Y (λ x → f) = f ∈ x ∶ X ⊢ Y
    syntax ∈⊢∶-syntax   X Y (λ y → f) = f ∈ X ⊢ y ∶ Y
    syntax ∈[]⊢-syntax  A Y        f  = f ∈[ A ]⊢ Y
    syntax ∈[]⊢∶-syntax A Y (λ y → f) = f ∈[ A ]⊢ y ∶ Y
    syntax ∈⊢[]-syntax  X B        f  = f ∈ X ⊢[ B ]
    syntax ∈∶⊢[]-syntax X B (λ x → f) = f ∈ x ∶  X ⊢[ B ]
```
```
    data NL◇_ : Judgement → Set where

      -- rules for fNL

      ◇ᴿ   : ∀ {X B f}
           →  f ∈ x ∶    X    ⊢[    B ]
           →  f ∈ x ∶ ⟨  X ⟩  ⊢[ ◇  B ]
```
``` hidden
      ax⁺  : ∀ {A} → x ∈ x ∶ · A · ⊢[ A ]
      ax⁻  : ∀ {B} → x ∈[ B ]⊢ x ∶ · B ·
      ↼    : ∀ {A Y f} {p : True (Negative? A)} →  f ∈[ A ]⊢ y ∶ Y    →  (app₁ {A} f) ∈ · A · ⊢  y ∶ Y
      ⇀    : ∀ {X B f} {p : True (Positive? B)} →  f ∈ x ∶ X ⊢[ B ]   →  (app₂ {B} f) ∈ x ∶ X ⊢ · B ·
      ↽    : ∀ {A Y f} {p : True (Positive? A)} →  f ∈ · A · ⊢ y ∶ Y  →  (app₃ {A} f) ∈[ A ]⊢ y ∶ Y
      ⇁    : ∀ {X B f} {p : True (Negative? B)} →  f ∈ x ∶ X ⊢ · B ·  →  (app₄ {B} f) ∈ x ∶ X ⊢[ B ]
      ⊗ᴸ   : ∀ {A B Y f} → f ∈ · A · ⊗ · B · ⊢ Y → f ∈ · A ⊗ B · ⊢ Y
      ⇒ᴸ   : ∀ {A B X Y f g} → f ∈ X ⊢[ A ] → g ∈[ B ]⊢ Y → (map f g) ∈[ A ⇒ B ]⊢ X ⇒ Y
      ⇐ᴸ   : ∀ {B A Y X f g} → f ∈ X ⊢[ A ] → g ∈[ B ]⊢ Y → (map g f) ∈[ B ⇐ A ]⊢ Y ⇐ X
      ⊗ᴿ   : ∀ {X Y A B f g} → f ∈ X ⊢[ A ] → g ∈ Y ⊢[ B ] → (map f g) ∈ X ⊗ Y ⊢[ A ⊗ B ]
      ⇒ᴿ   : ∀ {X A B f} → f ∈ X ⊢ · A · ⇒ · B · → f ∈ X ⊢ · A ⇒ B ·
      ⇐ᴿ   : ∀ {X B A f} → f ∈ X ⊢ · B · ⇐ · A · → f ∈ X ⊢ · B ⇐ A ·
      r⇒⊗  : ∀ {X Y Z f} → f ∈ Y ⊢ X ⇒ Z → (λ {(x , y) z → f y (x , z)}) ∈ X ⊗ Y ⊢ Z
      r⊗⇒  : ∀ {Y X Z f} → f ∈ X ⊗ Y ⊢ Z → (λ {y (x , z) → f (x , y) z}) ∈ Y ⊢ X ⇒ Z
      r⇐⊗  : ∀ {X Y Z f} → f ∈ X ⊢ Z ⇐ Y → (λ {(x , y) z → f x (z , y)}) ∈ X ⊗ Y ⊢ Z
      r⊗⇐  : ∀ {X Z Y f} → f ∈ X ⊗ Y ⊢ Z → (λ {x (z , y) → f (x , y) z}) ∈ X ⊢ Z ⇐ Y
```

``` hidden
module example where
  open import Data.Bool using (Bool)
  open import Data.List using (List; _∷_; [])
  open import Data.List.NonEmpty using (List⁺; _∷_)
  open import Data.Product using (_,_)
  open import Example.System.EXP public renaming (_,_ to _∙_)

  data Word : Set where
    mary leave to left wants said everyone
      : Word
```

```
  postulate
    MARY    : Entity
    PERSON  : Entity → Bool
    LEAVES  : Entity → Bool
    WANTS   : Entity → Bool → Bool
    SAID    : Entity → Bool → Bool
```

```
  Syn : Word → Type
  Syn mary      =    np
  Syn everyone  = (  np ⇐ n) ⊗ n
  Syn to        = (  np ⇒ s) ⇐ inf
  Syn leave     =    inf
  Syn left      =    np ⇒ s
  Syn wants     = (  np ⇒ s) ⇐    s
  Syn said      = (  np ⇒ s) ⇐ ◇  s
```

```
  Sem : (w : Word) → ⟦ Syn w ⟧⁺
  Sem mary      = MARY
  Sem everyone  = (λ{(p₁ , p₂) → FORALL (λ x → p₂ x ⊃ p₁ x)}) , PERSON
  Sem to        = (λ{((x , k) , p) → k (p x)})
  Sem leave     = LEAVES
  Sem left      = (λ{(x , k) → k (LEAVES x)})
  Sem wants     = (λ{((x , k) , y) → k (WANTS x (y id))})
  Sem said      = (λ{((x , k) , y) → k (SAID x (y id))})
```

```
  Lex : Word → List⁺ (Σ[ A ∈ Type ] ⟦ A ⟧⁺)
  Lex w = (Syn w , Sem w) ∷ []
```

``` hidden
  open Lexicon (fromLex grammar Lex) public using (interpret)

  example₁ :
```
```
    interpret (· mary · ∙ · wants · ∙ · everyone · ∙ · to · ∙ · leave ·)
      ↦  [ (λ k → FORALL (λ x → PERSON x ⊃ k (WANTS MARY (LEAVES x))))
         , (λ k → k (WANTS MARY (FORALL (λ x → PERSON x ⊃ LEAVES x))))
         ]
```
``` hidden
  example₁ = _
  example₂ :
```
```
    interpret (· mary · ∙ · said · ∙ ⟨ · everyone · ∙ · left · ⟩)
      ↦  (λ (k : Bool → Bool) → k (SAID MARY (FORALL (λ x → PERSON x ⊃ LEAVES x))))
```
``` hidden
  example₂ = _
```
