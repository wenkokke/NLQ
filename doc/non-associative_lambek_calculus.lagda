# Non-associative Lambek Calculus
``` hidden
module non-associative_lambek_calculus where

open import Logic.Polarity
```

## `SC`: Sequent calculus
```
module sequent_calculus (Atom : Set) where
```

[compute](Example/System/NL/SC.agda
  "asSyntaxDecl′ (quote Type) false []
    (quote el ∷ quote _⇒_ ∷ quote _⇐_ ∷ [])")

[compute](Example/System/NL/SC.agda
  "asSyntaxDecl (quote Structure)")

[compute](Example/System/NL/SC.agda
  "asSyntaxDecl (quote Context)")

[compute](Example/System/NL/SC.agda
  "asSyntaxDecl′ (quote Sequent) false (\"I\" ∷ \"J\" ∷ []) (quote _⊢_ ∷ [])")

[compute](Example/System/NL/SC.agda
  "asMathParOf (quote NL_)
    (quote ax ∷ quote cut ∷ quote ⇒L ∷ quote ⇒R ∷ quote ⇐L  ∷ quote ⇐R ∷ [])")


``` hidden
  infix  1 NL_
  infix  2 _⊢_
  infixr 6 _⇒_
  infixl 6 _⇐_
  infixr 4 _,>_
  infixl 4 _<,_
  infixr 4 _,_
  infixl 4 _[_]
```

```
  data Type : Set where
    el   : (A    : Atom)  → Type
    _⇒_  : (A B  : Type)  → Type
    _⇐_  : (B A  : Type)  → Type
```

```
  data Structure : Set where
    ·_·  : (A   : Type)       → Structure
    _,_  : (Γ Δ : Structure)  → Structure
```

```
  data Context : Set where
    []    : Context
    _<,_  : (Γ : Context)    (Δ : Structure)  → Context
    _,>_  : (Γ : Structure)  (Δ : Context)    → Context
```

```
  _[_] : Context → Structure → Structure
  []         [ Δ ] = Δ
  (Γ ,> Γ′)  [ Δ ] = Γ , (Γ′ [ Δ ])
  (Γ <, Γ′)  [ Δ ] = (Γ [ Δ ]) , Γ′
```

```
  data Sequent : Set where
    _⊢_ : (Γ : Structure) (A : Type) → Sequent
```

```
  data NL_ : Sequent → Set where

    ax   : ∀ {A}
         →  NL · A · ⊢ A
    cut  : ∀ {Γ Δ A B}
         →  NL Γ ⊢ A            →  NL Δ [ · A · ] ⊢ B  →  NL Δ [ Γ ] ⊢ B
    ⇒L   : ∀ {Γ Δ A B C}
         →  NL Γ [ · B · ] ⊢ C  →  NL Δ ⊢ A            →  NL Γ [ Δ , · A ⇒ B · ] ⊢ C
    ⇐L   : ∀ {Γ Δ A B C}
         →  NL Γ [ · B · ] ⊢ C  →  NL Δ ⊢ A            →  NL Γ [ · B ⇐ A · , Δ ] ⊢ C
    ⇒R   : ∀ {Γ A B}
         →  NL · A · , Γ ⊢ B    →  NL Γ ⊢ A ⇒ B
    ⇐R   : ∀ {Γ A B}
         →  NL Γ , · A · ⊢ B    →  NL Γ ⊢ B ⇐ A
```

[compute](Example/System/NL/SC.agda
  "asConstructorOf (quote Type) (quote _⊗_)")

[compute](Example/System/NL/SC.agda
  "asMathParOf (quote NL_) (quote ⊗L ∷ quote ⊗R ∷ [])")



## `R`: A combinator calculus with residuation

[compute](Example/System/NL/Res.agda
  "asSyntaxDecl′ (quote Sequent) false (\"I\" ∷ \"J\" ∷ []) (quote _⊢_ ∷ [])")

[compute](Example/System/NL/Res.agda
  "asMathPar (quote NL_)")



## `RM`: A cut-free combinator calculus

[compute](Example/System/NL/ResMon.agda
  "asMathPar (quote NL_)")

``` hidden
module Logic_NL_ResMon_Base_ax′ where
  open import Example.System.NL.ResMon hiding (ax′; cut′)

```
```
  ax′ : ∀ {A} → A ⊢NL A
  ax′ { A =  el    A  } = ax
  ax′ { A =  A  ⊗  B  } = m⊗  ax′ ax′
  ax′ { A =  A  ⇐  B  } = m⇐  ax′ ax′
  ax′ { A =  A  ⇒  B  } = m⇒  ax′ ax′
```

### An executable cut-elimination procedure

### Derivational Semantics

``` hidden
module ResMon→Agda (Atom : Set) where
  open import Data.Product using (_×_; _,_)
  open import Example.System.NL.ResMon hiding (⟦_⟧ᵗ; ⟦_⟧)
```

```
  ⟦_⟧ᵗ : Type → Set
  ⟦ el    A ⟧ᵗ = ⟦ A ⟧ᴬ
  ⟦ A  ⊗  B ⟧ᵗ = ⟦ A ⟧ᵗ  ×  ⟦ B ⟧ᵗ
  ⟦ A  ⇒  B ⟧ᵗ = ⟦ A ⟧ᵗ  →  ⟦ B ⟧ᵗ
  ⟦ B  ⇐  A ⟧ᵗ = ⟦ A ⟧ᵗ  →  ⟦ B ⟧ᵗ
```

```
  ⟦_⟧ : ∀ {A B} → A ⊢NL B → ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ
  ⟦ ax        ⟧ = λ x → x
  ⟦ m⊗   f g  ⟧ = λ{(x , y) → (⟦ f ⟧ x , ⟦ g ⟧ y)}
  ⟦ m⇒   f g  ⟧ = λ h x → ⟦ g ⟧ (h (⟦ f ⟧ x))
  ⟦ m⇐   f g  ⟧ = λ h x → ⟦ f ⟧ (h (⟦ g ⟧ x))
  ⟦ r⇒⊗  f    ⟧ = λ{(x , y) → ⟦ f ⟧ y x}
  ⟦ r⇐⊗  f    ⟧ = λ{(x , y) → ⟦ f ⟧ x y}
  ⟦ r⊗⇒  f    ⟧ = λ x y → ⟦ f ⟧ (y , x)
  ⟦ r⊗⇐  f    ⟧ = λ x y → ⟦ f ⟧ (x , y)

```



## `sNL`: Display Calculus
``` hidden
module DispCalc (Atom : Set) (Polarityᴬ? : Atom → Polarity) where

  open import Logic.NL.Type Atom
  open import Logic.NL.Type.Polarised Atom Polarityᴬ? using (Positive?; Negative?)
  open import Logic.NL.Structure.Polarised Atom
  open import Logic.NL.Sequent Atom
  open import Relation.Nullary.Decidable using (True)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  infix 1 NL_ _⊢NL_ _⊢NL[_] [_]⊢NL_
```

As @gore1998 puts it:

\begin{quote}
The Display Logic of Nuel Belnap is a general Gentzen-style proof
theoretical framework designed to capture many different logics in
one uniform setting. The beauty of display logic is a general
cut-elimination theorem, due to Belnap, which applies whenever the
rules of the display calculus obey certain, easily checked,
conditions.
\end{quote}

[compute](Example/System/NL.agda
  "asSyntaxDecl′ (quote Structure⁺) false (\"Γ⁺\" ∷ \"Δ⁺\" ∷ [])
    (quote Structure.·_· ∷ quote Structure._⊗_ ∷ [])")

[compute](Example/System/NL.agda
  "asSyntaxDecl′ (quote Structure⁻) false (\"Γ⁻\" ∷ \"Δ⁻\" ∷ [])
    (quote Structure.·_· ∷ quote Structure._⇒_ ∷ quote Structure._⇐_ ∷ [])")

[compute](Example/System/NL.agda
  "asSyntaxDecl′ (quote Sequent) false (\"I\" ∷ \"J\" ∷ [])
    (quote _⊢_ ∷ quote [_]⊢_ ∷ quote _⊢[_] ∷ [])")

[compute](Example/System/NL.agda
  "asMathPar (quote NL_)")



### `fNL`: Focusing & Polarity

```
  data Positive : Type → Set where
    el   : (A    : Atom)  → Polarityᴬ? A ≡ + → Positive (el A)
    _⊗_  : (A B  : Type)  → Positive (A ⊗ B)
```

```
  data Negative : Type → Set where
    el   : (A    : Atom)  → Polarityᴬ? A ≡ - → Negative (el A)
    _⇒_  : (A B  : Type)  → Negative (A ⇒ B)
    _⇐_  : (A B  : Type)  → Negative (A ⇐ B)
```

``` hidden
  mutual
   _⊢NL_ : Structure + → Structure - → Set
   X ⊢NL Y = NL X ⊢ Y
   _⊢NL[_] : Structure + → Type → Set
   X ⊢NL[ B ] = NL X ⊢[ B ]
   [_]⊢NL_ : Type → Structure - → Set
   [ A ]⊢NL Y = NL [ A ]⊢ Y
   data NL_ : Sequent → Set where
```
```
    ⇁  : ∀ {A X} {p : True (Negative?  A)} →  X ⊢NL · A ·  → X ⊢NL[ A ]
    ↽  : ∀ {A X} {p : True (Positive?  A)} →  · A · ⊢NL X  → [ A ]⊢NL X
    ⇀  : ∀ {A X} {p : True (Positive?  A)} →  X ⊢NL[ A ]   → X ⊢NL · A ·
    ↼  : ∀ {A X} {p : True (Negative?  A)} →  [ A ]⊢NL X   → · A · ⊢NL X
```
