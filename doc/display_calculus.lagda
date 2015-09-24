# Display Calculus
``` hidden
module display_calculus where

  open import Logic.Polarity
```

In this section, we will discuss the system of structural NL,
a fragment of the structural Lambek-Grishin calculus as introduced in
@moortgat2009. This calculus is the result of implementing the Lambek
calculus in the theoretical framework of display logic
[@belnap1982]. As @gore1998 puts it:

\begin{quote}
The Display Logic of Nuel Belnap is a general Gentzen-style proof
theoretical framework designed to capture many different logics in
one uniform setting. The beauty of display logic is a general
cut-elimination theorem, due to Belnap, which applies whenever the
rules of the display calculus obey certain, easily checked,
conditions.
\end{quote}

Working within the framework of display logic is an incredibly useful
tool for research, especially in the area of type-logical grammars, as
as it allows you to add and remove operators without having to worry
about things like maintaining a proof of cut-elimination.

However, as formalising the theory behind display logic is beyond the
scope of this thesis, we will only present the system that is the
*result* of the implementation in display logic. We can obtain a
cut-elimination procedure for this system from the proof of
equivalence with RM.

[compute](Example/System/NL.agda "asSyntaxDecl ('Γ' ∷ 'Δ' ∷ []) (quote Structure)")

[compute](Example/System/NL.agda "asSyntaxDecl ('I' ∷ 'J' ∷ []) (quote Sequent)")

[compute](Example/System/NL.agda "asMathPar (quote NL_)")


## Equivalence between RM and display calculus
``` hidden
module ResMon⇔DispCalc (Atom : Set) where
  open import Logic.NL.ResMon Atom as RM hiding (Type; el; _⊗_; _⇒_; _⇐_; cut′)
  open import Logic.NL        Atom as DC
```

```
  ⌊_⌋ : ∀ {p} → Structure p → Type
  ⌊  ·  A  ·  ⌋ = A
  ⌊  X  ⊗  Y  ⌋ = ⌊  X  ⌋ ⊗  ⌊  Y  ⌋
  ⌊  X  ⇒  Y  ⌋ = ⌊  X  ⌋ ⇒  ⌊  Y  ⌋
  ⌊  X  ⇐  Y  ⌋ = ⌊  X  ⌋ ⇐  ⌊  Y  ⌋
```

``` hidden
  mutual
```
```
    to   : ∀ {X Y} →       X  DC.⊢NL   Y    → ⌊  X ⌋  RM.⊢NL ⌊  Y ⌋
    toL  : ∀ {A Y} → DC.[  A  ]⊢NL     Y    →    A    RM.⊢NL ⌊  Y ⌋
    toR  : ∀ {X B} →       X  DC.⊢NL[  B ]  → ⌊  X ⌋  RM.⊢NL    B

    to   (  ⇀    f  )  = toR f
    to   (  ↼    f  )  = toL f
    to   (  ⊗L   f  )  = to f
    to   (  ⇒R   f  )  = to f
    to   (  ⇐R   f  )  = to f
    to   (  r⇒⊗  f  )  = r⇒⊗ (to f)
    to   (  r⊗⇒  f  )  = r⊗⇒ (to f)
    to   (  r⇐⊗  f  )  = r⇐⊗ (to f)
    to   (  r⊗⇐  f  )  = r⊗⇐ (to f)

    toL     ax⁻        = ax′
    toL  (  ↽    f  )  = to f
    toL  (  ⇒L   f g)  = m⇒  (toR f) (toL g)
    toL  (  ⇐L   f g)  = m⇐  (toL g) (toR f)

    toR     ax⁺        = ax′
    toR  (  ⇁    f  )  = to f
    toR  (  ⊗R   f g)  = m⊗  (toR f) (toR g)
```

```
  ⌈_⌉ : ∀ {p} → Type → Structure p
  ⌈_⌉ { p = +  }  (A  ⊗  B  )  = ⌈  A  ⌉ ⊗  ⌈  B  ⌉
  ⌈_⌉ { p = -  }  (A  ⇒  B  )  = ⌈  A  ⌉ ⇒  ⌈  B  ⌉
  ⌈_⌉ { p = -  }  (B  ⇐  A  )  = ⌈  B  ⌉ ⇐  ⌈  A  ⌉
  ⌈_⌉             (   A     )  = · A ·
```

``` hidden
  mutual
```
```
    deflateL : ∀ {A Y} → ⌈ A ⌉ DC.⊢NL Y → · A · DC.⊢NL Y
    deflateL {A = el   A} f = f
    deflateL {A = A ⇒  B} f = f
    deflateL {A = A ⇐  B} f = f
    deflateL {A = A ⊗  B} f = ⊗L (r⇐⊗ (deflateL (r⊗⇐ (r⇒⊗ (deflateL (r⊗⇒ f))))))

    deflateR : ∀ {X B} → X DC.⊢NL ⌈ B ⌉ → X DC.⊢NL · B ·
    deflateR {B = el   B} f = f
    deflateR {B = B ⇒  C} f = ⇒R (r⊗⇒ (deflateR (r⇐⊗ (deflateL (r⊗⇐ (r⇒⊗ f))))))
    deflateR {B = B ⇐  C} f = ⇐R (r⊗⇐ (deflateR (r⇒⊗ (deflateL (r⊗⇒ (r⇐⊗ f))))))
    deflateR {B = B ⊗  C} f = f
```

```
    from : ∀ {A B} → A RM.⊢NL B → ⌈ A ⌉ DC.⊢NL ⌈ B ⌉
    from (ax      )  = ⇀ ax⁺
    from (m⊗   f g)  = ⇀  (⊗R  (⇁ (deflateR (from f  ))) (⇁ (deflateR (from g  ))))
    from (m⇒   f g)  = ↼  (⇒L  (⇁ (deflateR (from f  ))) (↽ (deflateL (from g  ))))
    from (m⇐   f g)  = ↼  (⇐L  (⇁ (deflateR (from g  ))) (↽ (deflateL (from f  ))))
    from (r⇒⊗  f  )  = r⇒⊗ (from f)
    from (r⊗⇒  f  )  = r⊗⇒ (from f)
    from (r⇐⊗  f  )  = r⇐⊗ (from f)
    from (r⊗⇐  f  )  = r⊗⇐ (from f)
```

``` hidden
  mutual
```
```
    inflateL : ∀ {X Y} → ⌈ ⌊ X ⌋ ⌉ DC.⊢NL Y → X DC.⊢NL Y
    inflateL {X =  ·  A  ·  }  f = deflateL f
    inflateL {X =  X  ⊗  Y  }  f = r⇐⊗ (inflateL (r⊗⇐ (r⇒⊗ (inflateL (r⊗⇒ f)))))

    inflateR : ∀ {X Y} → X DC.⊢NL ⌈ ⌊ Y ⌋ ⌉ → X DC.⊢NL Y
    inflateR {Y =  ·  A  ·  }  f = deflateR f
    inflateR {Y =  X  ⇒  Y  }  f = r⊗⇒ (inflateR (r⇐⊗ (inflateL (r⊗⇐ (r⇒⊗ f)))))
    inflateR {Y =  X  ⇐  Y  }  f = r⊗⇐ (inflateR (r⇒⊗ (inflateL (r⊗⇒ (r⇐⊗ f)))))
```

Using the deflate/inflate approach, we can import theorems from the
algebraic axiomatisation---for instance, the cut rule:

```
  cut′ : ∀ {X A Y} → X DC.⊢NL[ A ] → DC.[ A ]⊢NL Y → X DC.⊢NL Y
  cut′ f g = inflateL (inflateR (from (RM.cut′ (toR f) (toL g))))
```

And once cut becomes available, we can derive the inverses of the left
and right rules, which convert logical formulas back to structures:

```
  ⊗L′  : ∀ {Y A B} → · A ⊗ B · DC.⊢NL Y  → · A · ⊗ · B · DC.⊢NL Y
  ⊗L′  f = cut′ (⊗R ax⁺ ax⁺) (↽ f)

  ⇒R′  : ∀ {X A B} → X DC.⊢NL · A ⇒ B · → X DC.⊢NL · A · ⇒ · B ·
  ⇒R′  f = cut′ (⇁ f) (⇒L ax⁺ ax⁻)

  ⇐R′  : ∀ {X A B} → X DC.⊢NL · B ⇐ A · → X DC.⊢NL · B · ⇐ · A ·
  ⇐R′  f = cut′ (⇁ f) (⇐L ax⁺ ax⁻)
```

And these inverses can be used to derive the logical equivalents of
the residuation rules:

```
  r⇒⊗′  : ∀ {A B C} → · B · DC.⊢NL · A ⇒ C ·  → · A ⊗ B · DC.⊢NL · C ·
  r⇒⊗′  f = ⊗L (r⇒⊗ (⇒R′ f))

  r⊗⇒′  : ∀ {A B C} → · A ⊗ B · DC.⊢NL · C ·  → · B · DC.⊢NL · A ⇒ C ·
  r⊗⇒′  f = ⇒R (r⊗⇒ (⊗L′ f))

  r⇐⊗′  : ∀ {A B C} → · A · DC.⊢NL · C ⇐ B ·  → · A ⊗ B · DC.⊢NL · C ·
  r⇐⊗′  f = ⊗L (r⇐⊗ (⇐R′ f))

  r⊗⇐′  : ∀ {A B C} → · A ⊗ B · DC.⊢NL · C ·  → · A · DC.⊢NL · C ⇐ B ·
  r⊗⇐′  f = ⇐R (r⊗⇐ (⊗L′ f))
```

Lastly, using these rules, we can define a second equivalence
between the algebraic and the structured versions of NL, namely one
which converts theorems in the algebraic system to algebraic
theorems in the structured system.

This equivalence is preferred, since there is no need to convert
between types and structures.

```
  from′ : ∀ {A B} → A RM.⊢NL B → · A · DC.⊢NL · B ·
  from′    ax         = ⇀ ax⁺
  from′ (  m⊗   f g)  = ⊗L (⇀ (⊗R (⇁ (from′ f)) (⇁ (from′ g))))
  from′ (  m⇒   f g)  = ⇒R (↼ (⇒L (⇁ (from′ f)) (↽ (from′ g))))
  from′ (  m⇐   f g)  = ⇐R (↼ (⇐L (⇁ (from′ g)) (↽ (from′ f))))
  from′ (  r⇒⊗  f  )  = r⇒⊗′ (from′ f)
  from′ (  r⊗⇒  f  )  = r⊗⇒′ (from′ f)
  from′ (  r⇐⊗  f  )  = r⇐⊗′ (from′ f)
  from′ (  r⊗⇐  f  )  = r⊗⇐′ (from′ f)
```



## Problems with Spurious Ambiguity
``` hidden
module spurious_ambiguity where

  open import Data.List using (length)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Example.System.Base using (Atom; N; NP; S; INF; _≟-Atom_)
  open import Logic.NL.Type                Atom
  open import Logic.NL.Sequent             Atom as NL
  open import Logic.NL.ResMon.Sequent      Atom as RM
  open import Logic.NL.Structure.Polarised Atom
  open import Logic.NL.Base                Atom
  open import Logic.NL.ProofSearch         Atom _≟-Atom_ renaming (findAll to findAllNL)
  open import Logic.NL.ResMon.ProofSearch  Atom _≟-Atom_ renaming (findAll to findAllRM)
```

``` hidden
  np n s inf : Type
  np  = el NP
  n   = el N
  s   = el S
  inf = el INF

  mary wants everyone to leave : Type
```
```
  mary      = np
  wants     = (np ⇒ s) ⇐ s
  everyone  = (np ⇐ n ) ⊗ n
  to        = ((np ⇒ s ) ⇐ inf)
  leave     = inf
```

``` hidden
  testRM :
```
```
    length (findAllRM (
      mary ⊗ wants ⊗ everyone ⊗ to ⊗ leave ⊢ s)) ≡ 11
```
``` hidden
  testRM = refl
```

``` hidden
  testNL :
```
```
    length (findAllNL (
      · mary · ⊗ · wants · ⊗ · everyone · ⊗ · to · ⊗ · leave · ⊢[ s ])) ≡ 1664
```
``` hidden
  testNL = refl
```



## Focusing and Polarity
``` hidden
module Pol (Atom : Set) (Polarityᴬ? : Atom → Polarity) where

  open import Relation.Nullary           using (Dec; yes; no)
  open import Relation.Nullary.Decidable using (True; toWitness)
  open import Relation.Binary.PropositionalEquality as P
  open import Logic.NL.Type Atom using (Type; el; _⇐_; _⊗_; _⇒_)
```


@moortgat2009

@bastenhof2012

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

We update the axiom and focusing rules from the system sNL with polarity
restrictions in the form of implicit polarity checks, thereby obtaining the
system fNL:


      ⇁    : ∀ {A X} {p : True (Negative?  A)} →  X ⊢fNL · A ·  → X ⊢fNL[ A ]
      ↽    : ∀ {A X} {p : True (Positive?  A)} →  · A · ⊢fNL X  → [ A ]⊢fNL X
      ⇀    : ∀ {A X} {p : True (Positive?  A)} →  X ⊢fNL[ A ]   → X ⊢fNL · A ·
      ↼    : ∀ {A X} {p : True (Negative?  A)} →  [ A ]⊢fNL X   → · A · ⊢fNL X


``` hidden
module non_spurious_ambiguity where

  open import Data.List using (length)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Example.NL.Pol renaming (_,_ to _∙_; parse to parsefNL)
```

``` hidden
  testNL :
```
```
    length (parsefNL (
      · mary · ∙ · wants · ∙ · everyone · ∙ · to · ∙ · leave ·)) ≡ 3
```
``` hidden
  testNL = refl
```
