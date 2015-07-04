``` hidden
module nl_derivational_semantics (Atom : Set) (⟦_⟧ᴬ : Atom → Set) where
```

## Derivational Semantics


### Translation to Linear Logic
``` hidden
module translation_to_ll where

  open import ll_base Atom ⟦_⟧ᴬ as ILL hiding (⟦_⟧; [_])
  open import nl_base Atom as NL
  open module RM = NL.ResMon using (RM_; ax; m⊗; m⇒; m⇐; r⇒⊗; r⊗⇒; r⇐⊗; r⊗⇐)
  open import Data.List using (List; _++_) renaming (_∷_ to _,_; [] to ∅)
```

```
  ⟦_⟧ : NL.Type → ILL.Type
  ⟦ el   A  ⟧ = el  A
  ⟦ A ⊗  B  ⟧ = ⟦ A ⟧ ⊗  ⟦ B ⟧
  ⟦ A ⇒  B  ⟧ = ⟦ A ⟧ ⊸  ⟦ B ⟧
  ⟦ B ⇐  A  ⟧ = ⟦ A ⟧ ⊸  ⟦ B ⟧
```

```
  [_] : ∀ {A B} → RM A RM.⊢ B → ILL ⟦ A ⟧ , ∅ ILL.⊢ ⟦ B ⟧
  [ ax        ] = ax
  [ m⊗   f g  ] = ⊗ₑ ax (⊗ᵢ [ f ] [ g ])
  [ m⇒   f g  ] = ⊸ᵢ (⊸ₑ (⊸ᵢ [ g  ]) (ex₁ (⊸ₑ ax [ f  ])))
  [ m⇐   f g  ] = ⊸ᵢ (⊸ₑ (⊸ᵢ [ f  ]) (ex₁ (⊸ₑ ax [ g  ])))
  [ r⇒⊗  f    ] = ⊗ₑ ax (ex₁  (⊸ₑ [ f ] ax))
  [ r⇐⊗  f    ] = ⊗ₑ ax (     (⊸ₑ [ f ] ax))
  [ r⊗⇒  f    ] = ⊸ᵢ (     (⊸ₑ (⊸ᵢ [ f ]) (⊗ᵢ ax ax)))
  [ r⊗⇐  f    ] = ⊸ᵢ (ex₁  (⊸ₑ (⊸ᵢ [ f ]) (⊗ᵢ ax ax)))
```



### Typing Agda programs
``` hidden
module typing_agda_programs where

  open import ll_base Atom ⟦_⟧ᴬ as LL using ()
  open import nl_base Atom      as NL using (Type; el; _⊗_; _⇒_; _⇐_)
  open import Function
  open import Data.Product

  infix  1 RM_
  infix  2 _⊢_∋_ ⊢∶-syntax ∶⊢-syntax
```

Let `⟦_⟧` now be the composition of the translation function above,
and the translation function from intuitionistic linear logic into Agda from
section \ref{intermezzo-linear-logic}.

``` hidden
  ⟦_⟧ : NL.Type → Set
  ⟦_⟧ = LL.⟦_⟧ ∘ translation_to_ll.⟦_⟧
```

We can now define judgements as follows

```
  data Judgement : Set where
    _⊢_∋_ : (A : Type) (B : Type) (f : ⟦ A ⟧ → ⟦ B ⟧) → Judgement
```

``` hidden
  ⊢∶-syntax : (A : Type) (B : Type) (f : ⟦ A ⟧ → ⟦ B ⟧) → Judgement
  ⊢∶-syntax = _⊢_∋_

  ∶⊢-syntax : (A : Type) (B : Type) (f : ⟦ A ⟧ → ⟦ B ⟧) → Judgement
  ∶⊢-syntax = _⊢_∋_
```

```
  syntax ⊢∶-syntax A B (λ x →  f)  = x  ∶ A ⊢ f ∶ B
  syntax ∶⊢-syntax A B         f   = f  ∶ A ⊢ B
```

```
  data RM_ : Judgement → Set where

    ax   : ∀ {A}
         →  RM x  ∶ el A ⊢ x ∶ el A

    m⊗   : ∀ {A B C D f g}
         →  RM f  ∶ A ⊢ B
         →  RM g  ∶ C ⊢ D
         →  RM x  ∶ A ⊗ C ⊢ (map f g x) ∶ B ⊗ D
    m⇒   : ∀ {A B C D f g}
         →  RM f  ∶ A ⊢ B
         →  RM g  ∶ C ⊢ D
         →  RM h  ∶ B ⇒ C ⊢ (g ∘ h ∘ f) ∶ A ⇒ D
    m⇐   : ∀ {A B C D f g}
         →  RM f  ∶ A ⊢ B
         →  RM g  ∶ C ⊢ D
         →  RM h  ∶ A ⇐ D ⊢ (f ∘ h ∘ g) ∶ B ⇐ C


    r⇒⊗  : ∀ {A B C f}
         →  RM f  ∶ B ⊢ A ⇒ C
         →  RM x  ∶ A ⊗ B ⊢ (uncurry (flip f) x) ∶ C
    r⊗⇒  : ∀ {A B C f}
         →  RM f  ∶ A ⊗ B ⊢ C
         →  RM x  ∶ B ⊢ (flip (curry f) x) ∶ A ⇒ C
    r⇐⊗  : ∀ {A B C f}
         →  RM f  ∶ A ⊢ C ⇐ B
         →  RM x  ∶ A ⊗ B ⊢ (uncurry f x) ∶ C
    r⊗⇐  : ∀ {A B C f}
         →  RM f  ∶ A ⊗ B ⊢ C
         →  RM x  ∶ A ⊢ (curry f x) ∶ C ⇐ B
```
