## Display Calculus
``` hidden
module nl_display_calculus (Atom : Set) where

open import Logic.Polarity
open import nl_base Atom using (Type; el; _⇐_; _⊗_; _⇒_) renaming (module ResMon to RM)
open RM hiding (Judgement; cut′)

infix  1  NL_
infix  10 ·_·
infixr 20 _⇒_ _⇐_
infixr 30 _⊗_
```


```
data Struct : Polarity → Set where
  ·_·  : {p  : Polarity}
       → (A  : Type)                      → Struct p
  _⊗_  : (Γ⁺ : Struct +) (Δ⁺ : Struct +)  → Struct +
  _⇒_  : (Γ⁺ : Struct +) (Δ⁻ : Struct -)  → Struct -
  _⇐_  : (Γ⁻ : Struct -) (Δ⁺ : Struct +)  → Struct -
```

``` hidden
module NL where

  infix  2  _⊢_
  infix  2  [_]⊢_
  infix  2  _⊢[_]
```
```
  data Judgement : Set where
    _⊢_    : Struct +  → Struct -  → Judgement
    [_]⊢_  : Type      → Struct -  → Judgement
    _⊢[_]  : Struct +  → Type      → Judgement
```
``` hidden
open NL public
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
  ⊗ᴿ   : ∀ {X Y A B} →  NL X ⊢[ A ] → NL Y ⊢[ B ] → NL X ⊗ Y ⊢[ A ⊗ B ]

  ⇒ᴸ   : ∀ {A B X Y} →  NL X ⊢[ A ] → NL [ B ]⊢ Y → NL [ A ⇒ B ]⊢ X ⇒ Y
  ⇒ᴿ   : ∀ {X A B}   →  NL X ⊢ · A · ⇒ · B · → NL X ⊢ · A ⇒ B ·

  ⇐ᴸ   : ∀ {B A Y X} →  NL X ⊢[ A ] → NL [ B ]⊢ Y → NL [ B ⇐ A ]⊢ Y ⇐ X
  ⇐ᴿ   : ∀ {X B A}   →  NL X ⊢ · B · ⇐ · A · → NL X ⊢ · B ⇐ A ·

  r⇒⊗  : ∀ {X Y Z}   →  NL Y ⊢ X ⇒ Z → NL X ⊗ Y ⊢ Z
  r⊗⇒  : ∀ {Y X Z}   →  NL X ⊗ Y ⊢ Z → NL Y ⊢ X ⇒ Z
  r⇐⊗  : ∀ {X Y Z}   →  NL X ⊢ Z ⇐ Y → NL X ⊗ Y ⊢ Z
  r⊗⇐  : ∀ {X Z Y}   →  NL X ⊗ Y ⊢ Z → NL X ⊢ Z ⇐ Y
```




### Equivalence between RM and display calculus

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
