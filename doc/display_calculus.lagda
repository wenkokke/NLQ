# Display Calculus
``` hidden
module display_calculus where

  open import Logic.Polarity
  open import non_associative_lambek_calculus
```

In this section, we will discuss the system of structural NL,
a fragment of the structural Lambek-Grishin calculus as introduced in
@moortgat2009. This calculus is the result of implementing the Lambek
calculus in the theoretical framework of display logic
[@belnap1982]. As @gore1998 puts it:

> The Display Logic of Nuel Belnap is a general Gentzen-style proof
> theoretical framework designed to capture many different logics in
> one uniform setting. The beauty of display logic is a general
> cut-elimination theorem, due to Belnap, which applies whenever the
> rules of the display calculus obey certain, easily checked,
> conditions.

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
  infix  2  _⊢_
  infix  2  [_]⊢_
  infix  2  _⊢[_]
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

```
  data NL_ : Judgement → Set where

    ax⁺  : ∀ {A}       →  NL · A · ⊢[ A ]
    ax⁻  : ∀ {B}       →  NL [ B ]⊢ · B ·

    ⇁    : ∀ {X B}     →  NL X ⊢ · B · → NL X ⊢[ B ]
    ↽    : ∀ {A Y}     →  NL · A · ⊢ Y → NL [ A ]⊢ Y
    ⇀    : ∀ {X B}     →  NL X ⊢[ B ] → NL X ⊢ · B ·
    ↼    : ∀ {A Y}     →  NL [ A ]⊢ Y → NL · A · ⊢ Y

    ⊗ᴸ   : ∀ {A B Y}   →  NL · A · ⊗ · B · ⊢ Y → NL · A ⊗ B · ⊢ Y
    ⇒ᴸ   : ∀ {A B X Y} →  NL X ⊢[ A ] → NL [ B ]⊢ Y → NL [ A ⇒ B ]⊢ X ⇒ Y
    ⇐ᴸ   : ∀ {B A Y X} →  NL X ⊢[ A ] → NL [ B ]⊢ Y → NL [ B ⇐ A ]⊢ Y ⇐ X

    ⊗ᴿ   : ∀ {X Y A B} →  NL X ⊢[ A ] → NL Y ⊢[ B ] → NL X ⊗ Y ⊢[ A ⊗ B ]
    ⇒ᴿ   : ∀ {X A B}   →  NL X ⊢ · A · ⇒ · B · → NL X ⊢ · A ⇒ B ·
    ⇐ᴿ   : ∀ {X B A}   →  NL X ⊢ · B · ⇐ · A · → NL X ⊢ · B ⇐ A ·

    r⇒⊗  : ∀ {X Y Z}   →  NL Y ⊢ X ⇒ Z → NL X ⊗ Y ⊢ Z
    r⊗⇒  : ∀ {Y X Z}   →  NL X ⊗ Y ⊢ Z → NL Y ⊢ X ⇒ Z
    r⇐⊗  : ∀ {X Y Z}   →  NL X ⊢ Z ⇐ Y → NL X ⊗ Y ⊢ Z
    r⊗⇐  : ∀ {X Z Y}   →  NL X ⊗ Y ⊢ Z → NL X ⊢ Z ⇐ Y
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
    to   : ∀ {X Y} →  NL    X  ⊢   Y    → RM ⌊  X ⌋  RM.⊢ ⌊  Y ⌋
    toᴸ  : ∀ {A Y} →  NL [  A ]⊢   Y    → RM    A    RM.⊢ ⌊  Y ⌋
    toᴿ  : ∀ {X B} →  NL    X  ⊢[  B ]  → RM ⌊  X ⌋  RM.⊢    B
  ```
  \begin{spec}
    to   : ∀ {X Y} →  NL    X    NL.⊢    Y    → RM ⌊  X ⌋  RM.⊢ ⌊  Y ⌋
    toᴸ  : ∀ {A Y} →  NL [  A ]  NL.⊢    Y    → RM    A    RM.⊢ ⌊  Y ⌋
    toᴿ  : ∀ {X B} →  NL    X    NL.⊢ [  B ]  → RM ⌊  X ⌋  RM.⊢    B
  \end{spec}
  ```
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
    deflateᴸ : ∀ {A Y} → NL ⌈ A ⌉ ⊢ Y → NL · A · ⊢ Y
    deflateᴸ {A = el   A} f = f
    deflateᴸ {A = A ⇒  B} f = f
    deflateᴸ {A = A ⇐  B} f = f
    deflateᴸ {A = A ⊗  B} f = ⊗ᴸ (r⇐⊗ (deflateᴸ (r⊗⇐ (r⇒⊗ (deflateᴸ (r⊗⇒ f))))))

    deflateᴿ : ∀ {X B} → NL X ⊢ ⌈ B ⌉ → NL X ⊢ · B ·
    deflateᴿ {B = el   B} f = f
    deflateᴿ {B = B ⇒  C} f = ⇒ᴿ (r⊗⇒ (deflateᴿ (r⇐⊗ (deflateᴸ (r⊗⇐ (r⇒⊗ f))))))
    deflateᴿ {B = B ⇐  C} f = ⇐ᴿ (r⊗⇐ (deflateᴿ (r⇒⊗ (deflateᴸ (r⊗⇒ (r⇐⊗ f))))))
    deflateᴿ {B = B ⊗  C} f = f
```

```
    from : ∀ {A B} → RM A RM.⊢ B → NL ⌈ A ⌉ NL.⊢ ⌈ B ⌉
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
    inflateᴸ : ∀ {X Y} → NL ⌈ ⌊ X ⌋ ⌉ ⊢ Y → NL X ⊢ Y
    inflateᴸ {X =  ·  A  ·  }  f = deflateᴸ f
    inflateᴸ {X =  X  ⊗  Y  }  f = r⇐⊗ (inflateᴸ (r⊗⇐ (r⇒⊗ (inflateᴸ (r⊗⇒ f)))))

    inflateᴿ : ∀ {X Y} → NL X ⊢ ⌈ ⌊ Y ⌋ ⌉ → NL X ⊢ Y
    inflateᴿ {Y =  ·  A  ·  }  f = deflateᴿ f
    inflateᴿ {Y =  X  ⇒  Y  }  f = r⊗⇒ (inflateᴿ (r⇐⊗ (inflateᴸ (r⊗⇐ (r⇒⊗ f)))))
    inflateᴿ {Y =  X  ⇐  Y  }  f = r⊗⇐ (inflateᴿ (r⇒⊗ (inflateᴸ (r⊗⇒ (r⇐⊗ f)))))
```

Using the deflate/inflate approach, we can import theorems from the
algebraic axiomatisation---for instance, the cut rule.


```
  cut′ : ∀ {X A Y} → NL X ⊢[ A ] → NL [ A ]⊢ Y → NL X ⊢ Y
  cut′ f g = inflateᴸ (inflateᴿ (from (RM.cut′ (toᴿ f) (toᴸ g))))
```

And once cut becomes available, we can derive the inverses of the invertible
rules.


```
  ⊗ᴸ′  : ∀ {Y A B} → NL · A ⊗ B · ⊢ Y  → NL · A · ⊗ · B · ⊢ Y
  ⊗ᴸ′  f = cut′ (⊗ᴿ ax⁺ ax⁺) (↽ f)

  ⇒ᴿ′  : ∀ {X A B} → NL X ⊢ · A ⇒ B ·  → NL X ⊢ · A · ⇒ · B ·
  ⇒ᴿ′  f = cut′ (⇁ f) (⇒ᴸ ax⁺ ax⁻)

  ⇐ᴿ′  : ∀ {X A B} → NL X ⊢ · B ⇐ A ·  → NL X ⊢ · B · ⇐ · A ·
  ⇐ᴿ′  f = cut′ (⇁ f) (⇐ᴸ ax⁺ ax⁻)
```

And use these to derive the logical equivalents of the structural residuation
rules.

```
  r⇒⊗′  : ∀ {A B C} → NL · B · ⊢ · A ⇒ C ·  → NL · A ⊗ B · ⊢ · C ·
  r⇒⊗′  f = ⊗ᴸ (r⇒⊗ (⇒ᴿ′ f))
  r⊗⇒′  : ∀ {A B C} → NL · A ⊗ B · ⊢ · C ·  → NL · B · ⊢ · A ⇒ C ·
  r⊗⇒′  f = ⇒ᴿ (r⊗⇒ (⊗ᴸ′ f))
  r⇐⊗′  : ∀ {A B C} → NL · A · ⊢ · C ⇐ B ·  → NL · A ⊗ B · ⊢ · C ·
  r⇐⊗′  f = ⊗ᴸ (r⇐⊗ (⇐ᴿ′ f))
  r⊗⇐′  : ∀ {A B C} → NL · A ⊗ B · ⊢ · C ·  → NL · A · ⊢ · C ⇐ B ·
  r⊗⇐′  f = ⇐ᴿ (r⊗⇐ (⊗ᴸ′ f))
```

Lastly, using these rules, we can define a second equivalence
between the algebraic and the structured versions of NL, namely one
which converts theorems in the algebraic system to algebraic
theorems in the structured system.

This equivalence is preferred, since there is no need to convert
between types and structures.

```
  from′ : ∀ {A B} → RM A RM.⊢ B → NL · A · NL.⊢ · B ·
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
  open import Logic.Intuitionistic.Ordered.Lambek.Type                Atom
  open import Logic.Intuitionistic.Ordered.Lambek.Judgement           Atom as NL
  open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Judgement    Atom as RM
  open import Logic.Intuitionistic.Ordered.Lambek.Structure.Polarised Atom
  open import Logic.Intuitionistic.Ordered.Lambek.Base                Atom
  open import Logic.Intuitionistic.Ordered.Lambek.ProofSearch         Atom _≟-Atom_ renaming (findAll to findAllNL)
  open import Logic.Intuitionistic.Ordered.Lambek.ResMon.ProofSearch  Atom _≟-Atom_ renaming (findAll to findAllRM)
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

    ⇁    : ∀ {A X} {p : True (Negative? A)}  → fNL  X ⊢ · A ·  → fNL X ⊢[ A ]
    ↽    : ∀ {A X} {p : True (Positive? A)}  → fNL  · A · ⊢ X  → fNL [ A ]⊢ X
    ⇀    : ∀ {A X} {p : True (Positive? A)}  → fNL  X ⊢[ A ]   → fNL X ⊢ · A ·
    ↼    : ∀ {A X} {p : True (Negative? A)}  → fNL  [ A ]⊢ X   → fNL · A · ⊢ X


    ⊗ᴸ   : ∀ {A B Y}    →  fNL · A · ⊗ · B · ⊢ Y → fNL · A ⊗ B · ⊢ Y
    ⇒ᴸ   : ∀ {A B X Y}  →  fNL X ⊢[ A ]  → fNL [ B ]⊢ Y  → fNL [ A ⇒ B ]⊢ X ⇒ Y
    ⇐ᴸ   : ∀ {B A Y X}  →  fNL X ⊢[ A ]  → fNL [ B ]⊢ Y  → fNL [ B ⇐ A ]⊢ Y ⇐ X

    ⊗ᴿ   : ∀ {X Y A B}  →  fNL X ⊢[ A ] → fNL Y ⊢[ B ] → fNL X ⊗ Y ⊢[ A ⊗ B ]
    ⇒ᴿ   : ∀ {X A B}    →  fNL X ⊢ · A · ⇒ · B ·  → fNL X ⊢ · A ⇒ B ·
    ⇐ᴿ   : ∀ {X B A}    →  fNL X ⊢ · B · ⇐ · A ·  → fNL X ⊢ · B ⇐ A ·


    r⇒⊗  : ∀ {X Y Z}    →  fNL Y ⊢ X ⇒ Z   → fNL X ⊗ Y ⊢ Z
    r⊗⇒  : ∀ {Y X Z}    →  fNL X ⊗ Y ⊢ Z   → fNL Y ⊢ X ⇒ Z
    r⇐⊗  : ∀ {X Y Z}    →  fNL X ⊢ Z ⇐ Y   → fNL X ⊗ Y ⊢ Z
    r⊗⇐  : ∀ {X Z Y}    →  fNL X ⊗ Y ⊢ Z   → fNL X ⊢ Z ⇐ Y
```


``` hidden
module non_spurious_ambiguity where

  open import Data.List using (length)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Example.System.PolNL
       hiding (mary; wants; everyone; to; leave) renaming (findAll to findAllNL)
```


``` hidden
  mary wants everyone to leave : Type
  mary      = np
  wants     = (np ⇒ s⁻) ⇐ s⁻
  everyone  = (np ⇐ n ) ⊗ n
  to        = ((np ⇒ s⁻ ) ⇐ inf)
  leave     = inf
```

``` hidden
  testNL :
```
```
    length (findAllNL (
      · mary · ⊗ · wants · ⊗ · everyone · ⊗ · to · ⊗ · leave · ⊢[ s⁻ ])) ≡ 3
```
``` hidden
  testNL = refl
```
