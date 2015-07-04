## Focusing and polarity
``` hidden
open import Logic.Polarity
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality as P

module nl_polarity (Atom : Set) (Polarityᴬ? : Atom → Polarity) where

  infix 1 fNL_
  open import nl_base Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open import nl_display_calculus Atom
```

@moortgat2009

@bastenhof2012

```
  data Positive : Type → Set where

    el   : (A    : Atom)  → Polarityᴬ? A ≡ + → Positive (el A)
    _⊗_  : (A B  : Type)  → Positive (A ⊗ B)
```
``` hidden
  Positive? : (A : Type) → Dec (Positive A)
  Positive? (el  A) with Polarityᴬ? A | inspect Polarityᴬ? A
  ...| + | P.[ A⁺ ] = yes (el A A⁺)
  ...| - | P.[ A⁻ ] = no (λ { (el .A A⁺) → +≠- (trans (sym A⁺) A⁻) })
  Positive? (A ⇒ B) = no (λ ())
  Positive? (A ⇐ B) = no (λ ())
  Positive? (A ⊗ B) = yes (A ⊗ B)
```
```
  data Negative : Type → Set where

    el   : (A    : Atom)  → Polarityᴬ? A ≡ - → Negative (el A)
    _⇒_  : (A B  : Type)  → Negative (A ⇒ B)
    _⇐_  : (A B  : Type)  → Negative (A ⇐ B)
```
``` hidden
  Negative? : (A : Type) → Dec (Negative A)
  Negative? (el  A) with Polarityᴬ? A | inspect Polarityᴬ? A
  ...| + | P.[ A⁺ ] = no (λ { (el .A A⁻) → +≠- (trans (sym A⁺) A⁻) })
  ...| - | P.[ A⁻ ] = yes (el A A⁻)
  Negative? (A ⇒ B) = yes (A ⇒ B)
  Negative? (A ⇐ B) = yes (A ⇐ B)
  Negative? (A ⊗ B) = no (λ ())
```

We update the axiom and focusing rules from the system sNL with polarity
restrictions in the form of implicit polarity checks, thereby obtaining the
system fNL:

\begin{truncated}
\begin{spec}
    ax⁺  : {True (Positive?  A)}  → fNL  ·  A  ·  ⊢  [  A  ]
    ax⁻  : {True (Negative?  B)}  → fNL  [  B  ]  ⊢  ·  B  ·

    ⇁    : {True (Negative?  B)}  → fNL     X     ⊢  ·  B  ·  → fNL     X     ⊢  [  B  ]
    ↽    : {True (Positive?  A)}  → fNL  ·  A  ·  ⊢     Y     → fNL  [  A  ]  ⊢     Y
    ⇀    : {True (Positive?  B)}  → fNL     X     ⊢  [  B  ]  → fNL     X     ⊢  ·  B  ·
    ↼    : {True (Negative?  A)}  → fNL  [  A  ]  ⊢     Y     → fNL  ·  A  ·  ⊢     Y
\end{spec}
\end{truncated}
``` hidden
  data fNL_ : Judgement → Set where

    ax⁺  : ∀ {A}        →  fNL · A · ⊢[ A ]
    ax⁻  : ∀ {B}        →  fNL [ B ]⊢ · B ·

    ⇁    : ∀ {X A} {p : True (Negative? A)}  → fNL  X ⊢ · A ·  → fNL X ⊢[ A ]
    ↽    : ∀ {X A} {p : True (Positive? A)}  → fNL  · A · ⊢ X  → fNL [ A ]⊢ X
    ⇀    : ∀ {X A} {p : True (Positive? A)}  → fNL  X ⊢[ A ]   → fNL X ⊢ · A ·
    ↼    : ∀ {X A} {p : True (Negative? A)}  → fNL  [ A ]⊢ X   → fNL · A · ⊢ X


    ⊗L   : ∀ {A B Y}    →  fNL · A · ⊗ · B · ⊢ Y → fNL · A ⊗ B · ⊢ Y
    ⇒L   : ∀ {A B X Y}  →  fNL X ⊢[ A ]  → fNL [ B ]⊢ Y  → fNL [ A ⇒ B ]⊢ X ⇒ Y
    ⇐L   : ∀ {B A Y X}  →  fNL X ⊢[ A ]  → fNL [ B ]⊢ Y  → fNL [ B ⇐ A ]⊢ Y ⇐ X

    ⊗R   : ∀ {X Y A B}  →  fNL X ⊢[ A ] → fNL Y ⊢[ B ] → fNL X ⊗ Y ⊢[ A ⊗ B ]
    ⇒R   : ∀ {X A B}    →  fNL X ⊢ · A · ⇒ · B ·  → fNL X ⊢ · A ⇒ B ·
    ⇐R   : ∀ {X B A}    →  fNL X ⊢ · B · ⇐ · A ·  → fNL X ⊢ · B ⇐ A ·


    r⇒⊗  : ∀ {X Y Z}    →  fNL Y ⊢ X ⇒ Z   → fNL X ⊗ Y ⊢ Z
    r⊗⇒  : ∀ {Y X Z}    →  fNL X ⊗ Y ⊢ Z   → fNL Y ⊢ X ⇒ Z
    r⇐⊗  : ∀ {X Y Z}    →  fNL X ⊢ Z ⇐ Y   → fNL X ⊗ Y ⊢ Z
    r⊗⇐  : ∀ {X Z Y}    →  fNL X ⊗ Y ⊢ Z   → fNL X ⊢ Z ⇐ Y
```
