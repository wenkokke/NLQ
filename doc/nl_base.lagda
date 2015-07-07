``` hidden
open import Logic.Polarity                             using (Polarity; +; -; +≠-)
open import Function                                   using (id; _∘_; flip)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Nullary.Decidable                 using (True)
open import Relation.Binary.PropositionalEquality as P hiding ([_])

module nl_base (Atom : Set) where

infixr 30 _⊗_
infixr 20 _⇒_
infixl 20 _⇐_
```

# The non-associative Lambek calculus

## Sequent calculus

due to @lambek1961

```
data Type : Set where
  el   : Atom  → Type
  _⊗_  : Type  → Type → Type
  _⇒_  : Type  → Type → Type
  _⇐_  : Type  → Type → Type
```

``` hidden
module SequentCalculus where

  infixr 1 SC_
  infix  2 _⊢_
  infixl 3 _[_]
  infixr 4 _∙_
  infixr 4 _∙>_
  infixl 4 _<∙_
```

```
  data Struct : Set where
    ·_·  : Type    → Struct
    _∙_  : Struct  → Struct → Struct
```

```
  data Context : Set where
    []    : Context
    _∙>_  : Struct   → Context  → Context
    _<∙_  : Context  → Struct   → Context
```

```
  _[_] : Context → Struct → Struct
  []       [ Δ ] = Δ
  Γ ∙> Γ′  [ Δ ] = Γ ∙ (Γ′ [ Δ ])
  Γ <∙ Γ′  [ Δ ] = (Γ [ Δ ]) ∙ Γ′
```

```
  data Judgement : Set where
    _⊢_ : Struct → Type → Judgement
```

[^syntax]


```
  data SC_ : Judgement → Set where
    ax   : ∀ {A}
         →  SC · A · ⊢ A

    cut  : ∀ {Γ Δ A B}
         →  SC Δ ⊢ A → SC Γ [ · A · ] ⊢ B → SC Γ [ Δ ] ⊢ B

    ⊗L   : ∀ {Γ A B C}
         →  SC Γ [ · A · ∙ · B · ] ⊢ C → SC Γ [ · A  ⊗ B · ] ⊢ C
    ⇒L   : ∀ {Γ Δ A B C}
         →  SC Γ [ · B · ]  ⊢ C  →  SC Δ ⊢ A  →  SC Γ [ Δ ∙ · A ⇒ B · ] ⊢ C
    ⇐L   : ∀ {Γ Δ A B C}
         →  SC Γ [ · B · ]  ⊢ C  →  SC Δ ⊢ A  →  SC Γ [ · B ⇐ A · ∙ Δ ] ⊢ C

    ⊗R   : ∀ {Γ Δ A B}
         →  SC Γ  ⊢ A → SC Δ ⊢ B → SC Γ ∙ Δ ⊢ A ⊗ B
    ⇒R   : ∀ {Γ A B}
         →  SC · A · ∙ Γ  ⊢ B  →  SC Γ  ⊢ A ⇒ B
    ⇐R   : ∀ {Γ A B}
         →  SC Γ ∙ · A ·  ⊢ B  →  SC Γ  ⊢ B ⇐ A
```

There are reasons in favour of and against the use of contexts. One
reason *for* the use of contexts is that it makes your proofs much
shorter, as we will see below. However, the reasons against using
contexts are that:

 1. it puts the plugging function `_[_]` in the return type of your
    data type definition, which usually leads to trouble with unification,
    and theories which are much more difficult to prove with [see @mcbride2014,
    pp. 298-299];

 2. it requires you to annotate your proofs with the contexts under
    which each rule is applied;

 3. it is hard to reduce spurious ambiguity in a sequent calculus
    which uses contexts, as the restrictions on the orders in which
    the rules can be applied have to be put on the contexts under
    which they are applied;


## The system with residuation R

due to @lambek1961

``` hidden
module ResCut where

  infix  1  R′_
  infix  2  _⊢_
```

```
  data Judgement : Set where
    _⊢_ : Type → Type → Judgement
```

```
  data R′_ : Judgement → Set where
    ax   : ∀ {A}      → R′ A ⊢ A

    cut  : ∀ {A B C}  → R′ A ⊢ B → R′ B ⊢ C → R′ A ⊢ C

    r⇒⊗  : ∀ {A B C}  → R′ B ⊢ A ⇒ C  → R′ A ⊗ B ⊢ C
    r⊗⇒  : ∀ {A B C}  → R′ A ⊗ B ⊢ C  → R′ B ⊢ A ⇒ C
    r⇐⊗  : ∀ {A B C}  → R′ A ⊢ C ⇐ B  → R′ A ⊗ B ⊢ C
    r⊗⇐  : ∀ {A B C}  → R′ A ⊗ B ⊢ C  → R′ A ⊢ C ⇐ B
```

```
  m⊗′  : ∀ {A B C D} → R′ A ⊢ B → R′ C ⊢ D → R′ A ⊗ C ⊢ B ⊗ D
  m⊗′  f g  = r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ (cut g (r⊗⇒ ax)))))

  m⇒′  : ∀ {A B C D} → R′ A ⊢ B → R′ C ⊢ D → R′ B ⇒ C ⊢ A ⇒ D
  m⇒′  f g  = r⊗⇒ (cut (r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ ax)))) g)

  m⇐′  : ∀ {A B C D} → R′ A ⊢ B → R′ C ⊢ D → R′ A ⇐ D ⊢ B ⇐ C
  m⇐′  f g  = r⊗⇐ (cut (r⇒⊗ (cut g (r⊗⇒ (r⇐⊗ ax)))) f)
```



### Equivalence between sequent calculus and R

We would like to be sure that the new axiomatisation for NL is
actually equally expressive.

``` hidden
module SC→R′ where

  module R′ = ResCut         ; open R′
  module SC = SequentCalculus; open SC hiding (Judgement)
```

```
  ⌊_⌋ : Struct → Type
  ⌊ · A ·  ⌋  = A
  ⌊ Γ ∙ Δ  ⌋  = ⌊ Γ ⌋ ⊗ ⌊ Δ ⌋
```

```
  cutIn′  : ∀ {Γ Δ Δ′ A}
          →  R′ ⌊ Δ ⌋ ⊢ ⌊ Δ′ ⌋
          →  R′ ⌊ Γ [ Δ′  ] ⌋ ⊢ A
          →  R′ ⌊ Γ [ Δ   ] ⌋ ⊢ A
  cutIn′ {Γ = []      } f g = cut f g
  cutIn′ {Γ = _ ∙> Γ  } f g = r⇒⊗ (cutIn′ {Γ = Γ} f (r⊗⇒ g))
  cutIn′ {Γ = Γ <∙ _  } f g = r⇐⊗ (cutIn′ {Γ = Γ} f (r⊗⇐ g))
```

```
  from : ∀ {Γ A} → SC Γ SC.⊢ A → R′ (⌊ Γ ⌋ R′.⊢ A)
  from    ax                  = ax
  from (  cut  {Γ = Γ}  f g)  = cutIn′ {Γ = Γ} (  from f)  (from g)
  from (  ⊗L   {Γ = Γ}  f)    = cutIn′ {Γ = Γ}    ax       (from f)
  from (  ⇒L   {Γ = Γ}  f g)  = cutIn′ {Γ = Γ} (r⇒⊗ (m⇒′ (from g) ax)) (from f)
  from (  ⇐L   {Γ = Γ}  f g)  = cutIn′ {Γ = Γ} (r⇐⊗ (m⇐′ ax (from g))) (from f)
  from (  ⊗R            f g)  = m⊗′  (from f) (from g)
  from (  ⇒R            f)    = r⊗⇒  (from f)
  from (  ⇐R            f)    = r⊗⇐  (from f)
```

```
  to : ∀ {A B} → R′ A R′.⊢ B → SC · A · SC.⊢ B
  to    ax         = ax
  to (  cut  f g)  = cut  {Γ = []} (to f) (to g)
  to (  r⇒⊗  f)    = ⊗L   {Γ = []} (cut {Γ = _ ∙> []} (to f) (⇒L {Γ = []} ax ax))
  to (  r⇐⊗  f)    = ⊗L   {Γ = []} (cut {Γ = [] <∙ _} (to f) (⇐L {Γ = []} ax ax))
  to (  r⊗⇒  f)    = ⇒R (cut {Γ = []} (⊗R ax ax) (to f))
  to (  r⊗⇐  f)    = ⇐R (cut {Γ = []} (⊗R ax ax) (to f))
```


We would also like to eliminate cut from out proofs, as it introduces
a new variable in the search and is always an applicable rule---we can
always *try* to search for a proof which connects our current proof to
our goal proof.

Unfortunately, in the system described above we cannot fully eliminate
cut. We will be left with the following atomic cuts, which correspond
to the introduction rules for the three connectives[^prime].




## The cut-free system RM

due to @moortgat1999

``` hidden
module ResMon where

  infix  1  RM_
  infixl 2  _⊢>_
  infixl 2  _<⊢_
  infixl 2  _[_]ᴶ
  infixl 10 _[_]
  infixr 20 _⇒>_ _<⇒_
  infixl 20 _⇐>_ _<⇐_
  infixr 30 _⊗>_ _<⊗_

  open ResCut public using (Judgement; _⊢_)
```


```
  data RM_ : Judgement → Set where
    ax   : ∀ {A}       → RM el A ⊢ el A

    m⊗   : ∀ {A B C D} → RM A ⊢ B  → RM C ⊢ D  → RM A ⊗ C ⊢ B ⊗ D
    m⇒   : ∀ {A B C D} → RM A ⊢ B  → RM C ⊢ D  → RM B ⇒ C ⊢ A ⇒ D
    m⇐   : ∀ {A B C D} → RM A ⊢ B  → RM C ⊢ D  → RM A ⇐ D ⊢ B ⇐ C

    r⇒⊗  : ∀ {A B C}   → RM B ⊢ A ⇒ C  → RM A ⊗ B ⊢ C
    r⊗⇒  : ∀ {A B C}   → RM A ⊗ B ⊢ C  → RM B ⊢ A ⇒ C
    r⇐⊗  : ∀ {A B C}   → RM A ⊢ C ⇐ B  → RM A ⊗ B ⊢ C
    r⊗⇐  : ∀ {A B C}   → RM A ⊗ B ⊢ C  → RM A ⊢ C ⇐ B
```

The reason we restrict the |ax| rule to atomic formulas is to limit spurious
ambiguity in proof search, but using monotonicity we can easily recover the
full axiom rule as |ax′| below:

```
  ax′ : ∀ {A} → RM A ⊢ A
  ax′ {A =  el   A  } = ax
  ax′ {A =  A ⊗  B  } = m⊗  ax′ ax′
  ax′ {A =  A ⇐  B  } = m⇐  ax′ ax′
  ax′ {A =  A ⇒  B  } = m⇒  ax′ ax′
```



### An executable cut-elimination procedure for RM

\begin{spec}
  data Polarity : Set where + - : Polarity
\end{spec}

```
  data Context (p : Polarity) : Polarity → Set where
    []    : Context p p
    _⊗>_  : Type         → Context p +  → Context p +
    _⇒>_  : Type         → Context p -  → Context p -
    _⇐>_  : Type         → Context p +  → Context p -
    _<⊗_  : Context p +  → Type         → Context p +
    _<⇒_  : Context p +  → Type         → Context p -
    _<⇐_  : Context p -  → Type         → Context p -
```

```
  _[_] : ∀ {p₁ p₂} → Context p₁ p₂ → Type → Type
  []      [ A ] = A
  B ⊗> C  [ A ] = B ⊗ (C [ A ])
  C <⊗ B  [ A ] = (C [ A ]) ⊗ B
  B ⇒> C  [ A ] = B ⇒ (C [ A ])
  C <⇒ B  [ A ] = (C [ A ]) ⇒ B
  B ⇐> C  [ A ] = B ⇐ (C [ A ])
  C <⇐ B  [ A ] = (C [ A ]) ⇐ B
```

```
  data Contextᴶ (p : Polarity) : Set where
    _<⊢_  : Context p +  → Type         → Contextᴶ p
    _⊢>_  : Type         → Context p -  → Contextᴶ p
```

```
  _[_]ᴶ : ∀ {p} → Contextᴶ p → Type → Judgement
  A <⊢ B [ C ]ᴶ = A [ C ] ⊢ B
  A ⊢> B [ C ]ᴶ = A ⊢ B [ C ]
```

``` hidden
  module el where

    data Origin {B} ( J : Contextᴶ + ) (f : RM J [ el B ]ᴶ) : Set where
         origin  : (f′ : ∀ {G} → RM G ⊢ el B → RM J [ G ]ᴶ)
                 → (pr : f ≡ f′ ax)
                 → Origin J f

    mutual
      view : ∀ {B} ( J : Contextᴶ + ) (f : RM J [ el B ]ᴶ) → Origin J f
      view ([] <⊢ ._)        ax         = origin id refl
      view ([] <⊢ ._)        (r⊗⇒ f)    = wrap {(_ ⊗> []) <⊢ _}               r⊗⇒   f
      view ([] <⊢ ._)        (r⊗⇐ f)    = wrap {([] <⊗ _) <⊢ _}               r⊗⇐   f
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = wrap {B <⊢ _}                (      m⊗ f) g
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = wrap {B <⊢ _}                       r⇒⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A ⊗> B)) <⊢ _}         r⊗⇒   f
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = wrap {_ ⊢> (_ ⇐> B)}                r⇐⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A ⊗> B) <⊗ _) <⊢ _}         r⊗⇐   f
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = wrap {A <⊢ _}                (flip  m⊗ g) f
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = wrap {_ ⊢> (A <⇒ _)}                r⇒⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A <⊗ B)) <⊢ _}         r⊗⇒   f
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = wrap {A <⊢ _}                       r⇐⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A <⊗ B) <⊗ _) <⊢ _}         r⊗⇐   f
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = wrap {_ ⊢> B}                (      m⇒ f) g
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇒> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = wrap {_ ⊢> B}                       r⊗⇒   f
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇒> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = wrap {B <⊢ _}                (      m⇐ f) g
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇐> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇐> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = wrap {(_ ⊗> B) <⊢ _}                r⊗⇐   f
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = wrap {A <⊢ _}                (flip  m⇒ g) f
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇒ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = wrap {(A <⊗ _) <⊢ _}                r⊗⇒   f
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇒ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = wrap {_ ⊢> A}                (flip  m⇐ g) f
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇐ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇐ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = wrap {_ ⊢> A}                       r⊗⇐   f

      wrap : ∀ { I : Contextᴶ + } { J : Contextᴶ + } {B}
           →   (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) (f : RM I [ el B ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin f′ pr = origin (g ∘ f′) (cong g pr)
```
```
  module ⊗ where
```
```
    data Origin {B C} ( J : Contextᴶ - ) (f : RM J [ B ⊗ C ]ᴶ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : RM E ⊢ B)
                 →  (h₂  : RM F ⊢ C)
                 →  (f′  : ∀ {G} → RM E ⊗ F ⊢ G → RM J [ G ]ᴶ)
                 →  (pr  : f ≡ f′ (m⊗ h₁ h₂))
                 →  Origin J f
```
``` hidden
    mutual
```
``` partial
      view : ∀ {B C} ( J : Contextᴶ - ) (f : RM J [ B ⊗ C ]ᴶ) → Origin J f
      view (._ ⊢> [])        (m⊗   f g)  =  origin f g id refl
      view (._ ⊢> [])        (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> [])      }         r⇒⊗    f
      view (._ ⊢> [])        (r⇐⊗  f)    =  wrap {_ ⊢> ([] <⇐ _)      }         r⇐⊗    f
      view ((_ ⊗> A) <⊢ ._)  (m⊗   f g)  =  wrap {A <⊢ _              }  (      m⊗ f)  g
      view ((_ ⊗> A) <⊢ ._)  (r⇒⊗  f)    =  wrap {A <⊢ _              }         r⇒⊗    f
      view ((_ ⊗> A) <⊢ ._)  (r⊗⇒  f)    =  wrap {(_ ⊗> (_ ⊗> A)) <⊢ _}         r⊗⇒    f
```
``` hidden
      view ((_ ⊗> A) <⊢ ._)  (r⇐⊗  f)    =  wrap {_ ⊢> (_ ⇐> A)       }         r⇐⊗    f
      view ((_ ⊗> A) <⊢ ._)  (r⊗⇐  f)    =  wrap {((_ ⊗> A) <⊗ _) <⊢ _}         r⊗⇐    f
      view ((A <⊗ _) <⊢ ._)  (m⊗   f g)  =  wrap {A <⊢ _              }  (flip  m⊗ g)  f
      view ((A <⊗ _) <⊢ ._)  (r⇒⊗  f)    =  wrap {_ ⊢> (A <⇒ _)       }         r⇒⊗    f
      view ((A <⊗ _) <⊢ ._)  (r⊗⇒  f)    =  wrap {(_ ⊗> (A <⊗ _)) <⊢ _}         r⊗⇒    f
      view ((A <⊗ _) <⊢ ._)  (r⇐⊗  f)    =  wrap {A <⊢ _              }         r⇐⊗    f
      view ((A <⊗ _) <⊢ ._)  (r⊗⇐  f)    =  wrap {((A <⊗ _) <⊗ _) <⊢ _}         r⊗⇐    f
      view (._ ⊢> (_ ⇒> A))  (m⇒   f g)  =  wrap {_ ⊢> A              }  (      m⇒ f)  g
      view (._ ⊢> (_ ⇒> A))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (_ ⇒> A))}         r⇒⊗    f
      view (._ ⊢> (_ ⇒> A))  (r⊗⇒  f)    =  wrap {_ ⊢> A              }         r⊗⇒    f
      view (._ ⊢> (_ ⇒> A))  (r⇐⊗  f)    =  wrap {_ ⊢> ((_ ⇒> A) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (_ ⇐> A))  (m⇐   f g)  =  wrap {A <⊢ _              }  (      m⇐ f)  g
      view (._ ⊢> (_ ⇐> A))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (_ ⇐> A))}         r⇒⊗    f
      view (._ ⊢> (_ ⇐> A))  (r⇐⊗  f)    =  wrap {_ ⊢> ((_ ⇐> A) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (_ ⇐> A))  (r⊗⇐  f)    =  wrap {(_ ⊗> A) <⊢ _       }         r⊗⇐    f
      view (._ ⊢> (A <⇒ _))  (m⇒   f g)  =  wrap {A <⊢ _              }  (flip  m⇒ g)  f
      view (._ ⊢> (A <⇒ _))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (A <⇒ _))}         r⇒⊗    f
      view (._ ⊢> (A <⇒ _))  (r⊗⇒  f)    =  wrap {(A <⊗ _) <⊢ _       }         r⊗⇒    f
      view (._ ⊢> (A <⇒ _))  (r⇐⊗  f)    =  wrap {_ ⊢> ((A <⇒ _) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (A <⇐ _))  (m⇐   f g)  =  wrap {_ ⊢> A              }  (flip  m⇐ g)  f
      view (._ ⊢> (A <⇐ _))  (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> (A <⇐ _))}         r⇒⊗    f
      view (._ ⊢> (A <⇐ _))  (r⇐⊗  f)    =  wrap {_ ⊢> ((A <⇐ _) <⇐ _)}         r⇐⊗    f
      view (._ ⊢> (A <⇐ _))  (r⊗⇐  f)    =  wrap {_ ⊢> A              }         r⊗⇐    f
```
```
      wrap : ∀ { I : Contextᴶ - } { J : Contextᴶ - } {B C}
           →  (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) (f : RM I [ B ⊗ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
```
``` hidden
  module ⇒ where

    data Origin {B C} ( J : Contextᴶ + ) (f : RM J [ B ⇒ C ]ᴶ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : RM E ⊢ B)
                 →  (h₂  : RM C ⊢ F)
                 →  (f′  : ∀ {G} → RM G ⊢ E ⇒ F → RM J [ G ]ᴶ)
                 →  (pr  : f ≡ f′ (m⇒ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextᴶ + ) (f : RM J [ B ⇒ C ]ᴶ) → Origin J f
      view ([] <⊢ ._)        (m⇒  f g)  = origin f g id refl
      view ([] <⊢ ._)        (r⊗⇒ f)    = wrap {(_ ⊗> []) <⊢ _}               r⊗⇒   f
      view ([] <⊢ ._)        (r⊗⇐ f)    = wrap {([] <⊗ _) <⊢ _}               r⊗⇐   f
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = wrap {B <⊢ _}                (      m⊗ f) g
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = wrap {B <⊢ _}                       r⇒⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A ⊗> B)) <⊢ _}         r⊗⇒   f
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = wrap {_ ⊢> (_ ⇐> B)}                r⇐⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A ⊗> B) <⊗ _) <⊢ _}         r⊗⇐   f
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = wrap {A <⊢ _}                (flip  m⊗ g) f
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = wrap {_ ⊢> (A <⇒ _)}                r⇒⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A <⊗ B)) <⊢ _}         r⊗⇒   f
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = wrap {A <⊢ _}                       r⇐⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A <⊗ B) <⊗ _) <⊢ _}         r⊗⇐   f
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = wrap {_ ⊢> B}                (      m⇒ f) g
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇒> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = wrap {_ ⊢> B}                       r⊗⇒   f
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇒> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = wrap {B <⊢ _}                (      m⇐ f) g
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇐> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇐> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = wrap {(_ ⊗> B) <⊢ _}                r⊗⇐   f
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = wrap {A <⊢ _}                (flip  m⇒ g) f
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇒ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = wrap {(A <⊗ _) <⊢ _}                r⊗⇒   f
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇒ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = wrap {_ ⊢> A}                (flip  m⇐ g) f
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇐ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇐ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = wrap {_ ⊢> A}                       r⊗⇐   f

      wrap : ∀ { I : Contextᴶ + } { J : Contextᴶ + } {B C}
           →  (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) (f : RM I [ B ⇒ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
```
``` hidden
  module ⇐ where

    data Origin {B C} ( J : Contextᴶ + ) (f : RM J [ B ⇐ C ]ᴶ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : RM B ⊢ E)
                 →  (h₂  : RM F ⊢ C)
                 →  (f′  : ∀ {G} → RM G ⊢ E ⇐ F → RM J [ G ]ᴶ)
                 →  (pr  : f ≡ f′ (m⇐ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextᴶ + ) (f : RM J [ B ⇐ C ]ᴶ) → Origin J f
      view ([] <⊢ ._)        (m⇐  f g)  = origin f g id refl
      view ([] <⊢ ._)        (r⊗⇒ f)    = wrap {(_ ⊗> []) <⊢ _}               r⊗⇒   f
      view ([] <⊢ ._)        (r⊗⇐ f)    = wrap {([] <⊗ _) <⊢ _}               r⊗⇐   f
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = wrap {B <⊢ _}                (      m⊗ f) g
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = wrap {B <⊢ _}                       r⇒⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A ⊗> B)) <⊢ _}         r⊗⇒   f
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = wrap {_ ⊢> (_ ⇐> B)}                r⇐⊗   f
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A ⊗> B) <⊗ _) <⊢ _}         r⊗⇐   f
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = wrap {A <⊢ _}                (flip  m⊗ g) f
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = wrap {_ ⊢> (A <⇒ _)}                r⇒⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = wrap {(_ ⊗> (A <⊗ B)) <⊢ _}         r⊗⇒   f
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = wrap {A <⊢ _}                       r⇐⊗   f
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = wrap {((A <⊗ B) <⊗ _) <⊢ _}         r⊗⇐   f
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = wrap {_ ⊢> B}                (      m⇒ f) g
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇒> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = wrap {_ ⊢> B}                       r⊗⇒   f
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇒> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = wrap {B <⊢ _}                (      m⇐ f) g
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A ⇐> B))}         r⇒⊗   f
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A ⇐> B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = wrap {(_ ⊗> B) <⊢ _}                r⊗⇐   f
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = wrap {A <⊢ _}                (flip  m⇒ g) f
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇒ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = wrap {(A <⊗ _) <⊢ _}                r⊗⇒   f
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇒ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = wrap {_ ⊢> A}                (flip  m⇐ g) f
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = wrap {_ ⊢> (_ ⇒> (A <⇐ B))}         r⇒⊗   f
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = wrap {_ ⊢> ((A <⇐ B) <⇐ _)}         r⇐⊗   f
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = wrap {_ ⊢> A}                       r⊗⇐   f

      wrap : ∀ { I : Contextᴶ + } { J : Contextᴶ + } {B C}
           →  (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) (f : RM I [ B ⇐ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
```

```
  cut′ : ∀ {A B C} → RM A ⊢ B → RM B ⊢ C → RM A ⊢ C
  cut′ {B = el B}       f  g   with el.view ([] <⊢ _) g
  ... | el.origin          g′  _ = g′ f
  cut′ {B = B₁ ⊗ B₂}    f  g   with ⊗.view (_ ⊢> []) f
  ... | ⊗.origin h₁ h₂  f′     _ = f′ (r⇐⊗ (cut′ h₁ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ g))))))
  cut′ {B = B₁ ⇐ B₂}    f  g   with ⇐.view ([] <⊢ _) g
  ... | ⇐.origin h₁ h₂     g′  _ = g′ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁)))))
  cut′ {B = B₁ ⇒ B₂}    f  g   with ⇒.view ([] <⊢ _) g
  ... | ⇒.origin h₁ h₂     g′  _ = g′ (r⊗⇒ (r⇐⊗ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂)))))
```



### Equivalence between R and RM

``` hidden
module R′→RM where

  module RM = ResMon ; open RM
  module R′ = ResCut ; open R′
```

```
  from : ∀ {A B} → R′ A R′.⊢ B → RM A RM.⊢ B
  from  ax         = ax′
  from (cut  f g)  = cut′  (from f) (from g)
  from (r⇒⊗  f)    = r⇒⊗   (from f)
  from (r⊗⇒  f)    = r⊗⇒   (from f)
  from (r⇐⊗  f)    = r⇐⊗   (from f)
  from (r⊗⇐  f)    = r⊗⇐   (from f)
```

```
  to : ∀ {A B} → RM A RM.⊢ B → R′ A R′.⊢ B
  to  ax         = ax
  to (m⊗   f g)  = m⊗′  (to f) (to g)
  to (m⇒   f g)  = m⇒′  (to f) (to g)
  to (m⇐   f g)  = m⇐′  (to f) (to g)
  to (r⇒⊗  f)    = r⇒⊗  (to f)
  to (r⊗⇒  f)    = r⊗⇒  (to f)
  to (r⇐⊗  f)    = r⇐⊗  (to f)
  to (r⊗⇐  f)    = r⊗⇐  (to f)
```


[^prime]:  I have made it convention to label all derived and admissible rules
           with a prime. This makes it clear (without syntax highlighting) which
           rules are atomic in a system.
[^syntax]: In place of the full version (e.g. |SC_ Γ ⊢ A|) I will simply write
           |Γ ⊢ A| for judgements, and use superscripts to disambiguate when
           necessary (i.e. |Γ SC.⊢ A|).
