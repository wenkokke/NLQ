# Display Calculus
``` hidden
module display_calculus where

  open import Logic.Polarity
  open import non-associative_lambek_calculus
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

``` hidden
module display_calculus (Atom : Set) where

  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  infix  1  NL_
  infix  10 ·_·
  infixr 20 _⇒_ _⇐_
  infixr 30 _⊗_
  infix  2  _⊢_ _⊢NL_
  infix  2  [_]⊢_ [_]⊢NL_
  infix  2  _⊢[_] _⊢NL[_]
```

```
  data Struct : Polarity → Set where
    ·_·  : {p  : Polarity}
         → (A  : Type)                      → Struct p
    _⊗_  : (Γ⁺ : Struct +) (Δ⁺ : Struct +)  → Struct +
    _⇒_  : (Γ⁺ : Struct +) (Δ⁻ : Struct -)  → Struct -
    _⇐_  : (Γ⁻ : Struct -) (Δ⁺ : Struct +)  → Struct -
```

```
  data Judgement : Set where
    _⊢_    : Struct +  → Struct -  → Judgement
    [_]⊢_  : Type      → Struct -  → Judgement
    _⊢[_]  : Struct +  → Type      → Judgement
```

``` hidden
  mutual
    _⊢NL_ : Struct + → Struct - → Set
    X ⊢NL Y = NL X ⊢ Y
    _⊢NL[_] : Struct + → Type → Set
    X ⊢NL[ B ] = NL X ⊢[ B ]
    [_]⊢NL_ : Type → Struct - → Set
    [ A ]⊢NL Y = NL [ A ]⊢ Y
```
```
    data NL_ : Judgement → Set where

      ax⁺  : ∀ {A}       →  · A · ⊢NL[ A ]
      ax⁻  : ∀ {B}       →  [ B ]⊢NL · B ·

      ⇁    : ∀ {X B}     →  X ⊢NL · B · → X ⊢NL[ B ]
      ↽    : ∀ {A Y}     →  · A · ⊢NL Y → [ A ]⊢NL Y
      ⇀    : ∀ {X B}     →  X ⊢NL[ B ] → X ⊢NL · B ·
      ↼    : ∀ {A Y}     →  [ A ]⊢NL Y → · A · ⊢NL Y

      ⊗ᴸ   : ∀ {A B Y}   →  · A · ⊗ · B · ⊢NL Y → · A ⊗ B · ⊢NL Y
      ⇒ᴸ   : ∀ {A B X Y} →  X ⊢NL[ A ] → [ B ]⊢NL Y → [ A ⇒ B ]⊢NL X ⇒ Y
      ⇐ᴸ   : ∀ {B A Y X} →  X ⊢NL[ A ] → [ B ]⊢NL Y → [ B ⇐ A ]⊢NL Y ⇐ X

      ⊗ᴿ   : ∀ {X Y A B} →  X ⊢NL[ A ] → Y ⊢NL[ B ] → X ⊗ Y ⊢NL[ A ⊗ B ]
      ⇒ᴿ   : ∀ {X A B}   →  X ⊢NL · A · ⇒ · B · → X ⊢NL · A ⇒ B ·
      ⇐ᴿ   : ∀ {X B A}   →  X ⊢NL · B · ⇐ · A · → X ⊢NL · B ⇐ A ·

      r⇒⊗  : ∀ {X Y Z}   →  Y ⊢NL X ⇒ Z → X ⊗ Y ⊢NL Z
      r⊗⇒  : ∀ {Y X Z}   →  X ⊗ Y ⊢NL Z → Y ⊢NL X ⇒ Z
      r⇐⊗  : ∀ {X Y Z}   →  X ⊢NL Z ⇐ Y → X ⊗ Y ⊢NL Z
      r⊗⇐  : ∀ {X Z Y}   →  X ⊗ Y ⊢NL Z → X ⊢NL Z ⇐ Y
```


## Equivalence between RM and display calculus
``` hidden
module resmon⇔display_calculus (Atom : Set) where

  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  module RM = resmon           Atom ; open RM hiding (Judgement; cut′)
  module NL = display_calculus Atom ; open NL
```

```
  ⌊_⌋ : ∀ {p} → Struct p → Type
  ⌊  ·  A  ·  ⌋ = A
  ⌊  X  ⊗  Y  ⌋ = ⌊  X  ⌋ ⊗  ⌊  Y  ⌋
  ⌊  X  ⇒  Y  ⌋ = ⌊  X  ⌋ ⇒  ⌊  Y  ⌋
  ⌊  X  ⇐  Y  ⌋ = ⌊  X  ⌋ ⇐  ⌊  Y  ⌋
```

``` hidden
  mutual
```
```
    to   : ∀ {X Y} →       X  NL.⊢NL   Y    → ⌊  X ⌋  RM.⊢RM ⌊  Y ⌋
    toᴸ  : ∀ {A Y} → NL.[  A  ]⊢NL     Y    →    A    RM.⊢RM ⌊  Y ⌋
    toᴿ  : ∀ {X B} →       X  NL.⊢NL[  B ]  → ⌊  X ⌋  RM.⊢RM    B

    to   (  ⇀    f  )  = toᴿ f
    to   (  ↼    f  )  = toᴸ f
    to   (  ⊗ᴸ   f  )  = to f
    to   (  ⇒ᴿ   f  )  = to f
    to   (  ⇐ᴿ   f  )  = to f
    to   (  r⇒⊗  f  )  = r⇒⊗ (to f)
    to   (  r⊗⇒  f  )  = r⊗⇒ (to f)
    to   (  r⇐⊗  f  )  = r⇐⊗ (to f)
    to   (  r⊗⇐  f  )  = r⊗⇐ (to f)

    toᴸ     ax⁻        = ax′
    toᴸ  (  ↽    f  )  = to f
    toᴸ  (  ⇒ᴸ   f g)  = m⇒  (toᴿ f) (toᴸ g)
    toᴸ  (  ⇐ᴸ   f g)  = m⇐  (toᴸ g) (toᴿ f)

    toᴿ     ax⁺        = ax′
    toᴿ  (  ⇁    f  )  = to f
    toᴿ  (  ⊗ᴿ   f g)  = m⊗  (toᴿ f) (toᴿ g)
```

```
  ⌈_⌉ : ∀ {p} → Type → Struct p
  ⌈_⌉ { p = +  }  (A  ⊗  B  )  = ⌈  A  ⌉ ⊗  ⌈  B  ⌉
  ⌈_⌉ { p = -  }  (A  ⇒  B  )  = ⌈  A  ⌉ ⇒  ⌈  B  ⌉
  ⌈_⌉ { p = -  }  (B  ⇐  A  )  = ⌈  B  ⌉ ⇐  ⌈  A  ⌉
  ⌈_⌉             (   A     )  = · A ·
```

``` hidden
  mutual
```
```
    deflateᴸ : ∀ {A Y} → ⌈ A ⌉ ⊢NL Y → · A · ⊢NL Y
    deflateᴸ {A = el   A} f = f
    deflateᴸ {A = A ⇒  B} f = f
    deflateᴸ {A = A ⇐  B} f = f
    deflateᴸ {A = A ⊗  B} f = ⊗ᴸ (r⇐⊗ (deflateᴸ (r⊗⇐ (r⇒⊗ (deflateᴸ (r⊗⇒ f))))))

    deflateᴿ : ∀ {X B} → X ⊢NL ⌈ B ⌉ → X ⊢NL · B ·
    deflateᴿ {B = el   B} f = f
    deflateᴿ {B = B ⇒  C} f = ⇒ᴿ (r⊗⇒ (deflateᴿ (r⇐⊗ (deflateᴸ (r⊗⇐ (r⇒⊗ f))))))
    deflateᴿ {B = B ⇐  C} f = ⇐ᴿ (r⊗⇐ (deflateᴿ (r⇒⊗ (deflateᴸ (r⊗⇒ (r⇐⊗ f))))))
    deflateᴿ {B = B ⊗  C} f = f
```

```
    from : ∀ {A B} → A RM.⊢RM B → ⌈ A ⌉ NL.⊢NL ⌈ B ⌉
    from (ax      )  = ⇀ ax⁺
    from (m⊗   f g)  = ⇀  (⊗ᴿ  (⇁ (deflateᴿ (from f  ))) (⇁ (deflateᴿ (from g  ))))
    from (m⇒   f g)  = ↼  (⇒ᴸ  (⇁ (deflateᴿ (from f  ))) (↽ (deflateᴸ (from g  ))))
    from (m⇐   f g)  = ↼  (⇐ᴸ  (⇁ (deflateᴿ (from g  ))) (↽ (deflateᴸ (from f  ))))
    from (r⇒⊗  f  )  = r⇒⊗ (from f)
    from (r⊗⇒  f  )  = r⊗⇒ (from f)
    from (r⇐⊗  f  )  = r⇐⊗ (from f)
    from (r⊗⇐  f  )  = r⊗⇐ (from f)
```

``` hidden
  mutual
```
```
    inflateᴸ : ∀ {X Y} → ⌈ ⌊ X ⌋ ⌉ ⊢NL Y → X ⊢NL Y
    inflateᴸ {X =  ·  A  ·  }  f = deflateᴸ f
    inflateᴸ {X =  X  ⊗  Y  }  f = r⇐⊗ (inflateᴸ (r⊗⇐ (r⇒⊗ (inflateᴸ (r⊗⇒ f)))))

    inflateᴿ : ∀ {X Y} → X ⊢NL ⌈ ⌊ Y ⌋ ⌉ → X ⊢NL Y
    inflateᴿ {Y =  ·  A  ·  }  f = deflateᴿ f
    inflateᴿ {Y =  X  ⇒  Y  }  f = r⊗⇒ (inflateᴿ (r⇐⊗ (inflateᴸ (r⊗⇐ (r⇒⊗ f)))))
    inflateᴿ {Y =  X  ⇐  Y  }  f = r⊗⇐ (inflateᴿ (r⇒⊗ (inflateᴸ (r⊗⇒ (r⇐⊗ f)))))
```

Using the deflate/inflate approach, we can import theorems from the
algebraic axiomatisation---for instance, the cut rule:

```
  cut′ : ∀ {X A Y} → X ⊢NL[ A ] → [ A ]⊢NL Y → X ⊢NL Y
  cut′ f g = inflateᴸ (inflateᴿ (from (RM.cut′ (toᴿ f) (toᴸ g))))
```

And once cut becomes available, we can derive the inverses of the left
and right rules, which convert logical formulas back to structures:

```
  ⊗ᴸ′  : ∀ {Y A B} → · A ⊗ B · ⊢NL Y  → · A · ⊗ · B · ⊢NL Y
  ⊗ᴸ′  f = cut′ (⊗ᴿ ax⁺ ax⁺) (↽ f)

  ⇒ᴿ′  : ∀ {X A B} → X ⊢NL · A ⇒ B · → X ⊢NL · A · ⇒ · B ·
  ⇒ᴿ′  f = cut′ (⇁ f) (⇒ᴸ ax⁺ ax⁻)

  ⇐ᴿ′  : ∀ {X A B} → X ⊢NL · B ⇐ A · → X ⊢NL · B · ⇐ · A ·
  ⇐ᴿ′  f = cut′ (⇁ f) (⇐ᴸ ax⁺ ax⁻)
```

And these inverses can be used to derive the logical equivalents of
the residuation rules:

```
  r⇒⊗′  : ∀ {A B C} → · B · ⊢NL · A ⇒ C ·  → · A ⊗ B · ⊢NL · C ·
  r⇒⊗′  f = ⊗ᴸ (r⇒⊗ (⇒ᴿ′ f))

  r⊗⇒′  : ∀ {A B C} → · A ⊗ B · ⊢NL · C ·  → · B · ⊢NL · A ⇒ C ·
  r⊗⇒′  f = ⇒ᴿ (r⊗⇒ (⊗ᴸ′ f))

  r⇐⊗′  : ∀ {A B C} → · A · ⊢NL · C ⇐ B ·  → · A ⊗ B · ⊢NL · C ·
  r⇐⊗′  f = ⊗ᴸ (r⇐⊗ (⇐ᴿ′ f))

  r⊗⇐′  : ∀ {A B C} → · A ⊗ B · ⊢NL · C ·  → · A · ⊢NL · C ⇐ B ·
  r⊗⇐′  f = ⇐ᴿ (r⊗⇐ (⊗ᴸ′ f))
```

Lastly, using these rules, we can define a second equivalence
between the algebraic and the structured versions of NL, namely one
which converts theorems in the algebraic system to algebraic
theorems in the structured system.

This equivalence is preferred, since there is no need to convert
between types and structures.

```
  from′ : ∀ {A B} → A RM.⊢RM B → · A · NL.⊢NL · B ·
  from′    ax         = ⇀ ax⁺
  from′ (  m⊗   f g)  = ⊗ᴸ (⇀ (⊗ᴿ (⇁ (from′ f)) (⇁ (from′ g))))
  from′ (  m⇒   f g)  = ⇒ᴿ (↼ (⇒ᴸ (⇁ (from′ f)) (↽ (from′ g))))
  from′ (  m⇐   f g)  = ⇐ᴿ (↼ (⇐ᴸ (⇁ (from′ g)) (↽ (from′ f))))
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
  open import Logic.NL.Judgement           Atom as NL
  open import Logic.NL.ResMon.Judgement    Atom as RM
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
module focpol (Atom : Set) (Polarityᴬ? : Atom → Polarity) where

  open import Relation.Nullary           using (Dec; yes; no)
  open import Relation.Nullary.Decidable using (True; toWitness)
  open import Relation.Binary.PropositionalEquality as P
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open display_calculus Atom using (Struct; ·_·; _⇐_; _⊗_; _⇒_; Judgement; _⊢_; [_]⊢_; _⊢[_])
  infix 1 fNL_
  infix 2 _⊢fNL_ [_]⊢fNL_ _⊢fNL[_]
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

``` hidden
  mutual
    _⊢fNL_ : Struct + → Struct - → Set
    X ⊢fNL Y = fNL X ⊢ Y
    _⊢fNL[_] : Struct + → Type → Set
    X ⊢fNL[ B ] = fNL X ⊢[ B ]
    [_]⊢fNL_ : Type → Struct - → Set
    [ A ]⊢fNL Y = fNL [ A ]⊢ Y
```
``` hidden
    data fNL_ : Judgement → Set where

      ax⁺  : ∀ {A}        →  · A · ⊢fNL[ A ]
      ax⁻  : ∀ {B}        →  [ B ]⊢fNL · B ·
```
```
      ⇁    : ∀ {A X} {p : True (Negative?  A)} →  X ⊢fNL · A ·  → X ⊢fNL[ A ]
      ↽    : ∀ {A X} {p : True (Positive?  A)} →  · A · ⊢fNL X  → [ A ]⊢fNL X
      ⇀    : ∀ {A X} {p : True (Positive?  A)} →  X ⊢fNL[ A ]   → X ⊢fNL · A ·
      ↼    : ∀ {A X} {p : True (Negative?  A)} →  [ A ]⊢fNL X   → · A · ⊢fNL X
```
``` hidden
      ⊗ᴸ   : ∀ {A B Y}    →  · A · ⊗ · B · ⊢fNL Y → · A ⊗ B · ⊢fNL Y
      ⇒ᴸ   : ∀ {A B X Y}  →  X ⊢fNL[ A ]  → [ B ]⊢fNL Y  → [ A ⇒ B ]⊢fNL X ⇒ Y
      ⇐ᴸ   : ∀ {B A Y X}  →  X ⊢fNL[ A ]  → [ B ]⊢fNL Y  → [ B ⇐ A ]⊢fNL Y ⇐ X

      ⊗ᴿ   : ∀ {X Y A B}  →  X ⊢fNL[ A ] → Y ⊢fNL[ B ] → X ⊗ Y ⊢fNL[ A ⊗ B ]
      ⇒ᴿ   : ∀ {X A B}    →  X ⊢fNL · A · ⇒ · B ·  → X ⊢fNL · A ⇒ B ·
      ⇐ᴿ   : ∀ {X B A}    →  X ⊢fNL · B · ⇐ · A ·  → X ⊢fNL · B ⇐ A ·


      r⇒⊗  : ∀ {X Y Z}    →  Y ⊢fNL X ⇒ Z   → X ⊗ Y ⊢fNL Z
      r⊗⇒  : ∀ {Y X Z}    →  X ⊗ Y ⊢fNL Z   → Y ⊢fNL X ⇒ Z
      r⇐⊗  : ∀ {X Y Z}    →  X ⊢fNL Z ⇐ Y   → X ⊗ Y ⊢fNL Z
      r⊗⇐  : ∀ {X Z Y}    →  X ⊗ Y ⊢fNL Z   → X ⊢fNL Z ⇐ Y
```


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
