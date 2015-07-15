# Non-associative Lambek Calculus
``` hidden
module non_associative_lambek_calculus where
```

In this section we will discuss the non-associative Lambek calculus,
which forms the basis of most categorial grammar and type-logical
grammar systems.



## Sequent Calculus
``` hidden
module sequent_calculus (Atom : Set) where

  infixr 1 SC_
  infix  2 _⊢_
  infixl 3 _[_]
  infix  4 _∙_ _∙>_ _<∙_
  infixr 30 _⊗_
  infixr 20 _⇒_
  infixl 20 _⇐_
```

due to @lambek1961

```
  data Type : Set where
    el   : Atom  → Type
    _⊗_  : Type  → Type → Type
    _⇒_  : Type  → Type → Type
    _⇐_  : Type  → Type → Type
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
``` hidden
module res (Atom : Set) where

  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  infix  1  R′_
  infix  2  _⊢_
```

due to @lambek1961

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
``` hidden
module sequent_calculus⇔res (Atom : Set) where

  module R′ = res              Atom ; open R′ hiding (Judgement)
  module SC = sequent_calculus Atom ; open SC hiding (Judgement)
```

We would like to be sure that the new axiomatisation for NL is
actually equally expressive.

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
``` hidden
module resmon (Atom : Set) where

  infix  1  RM_
  infixl 2  _⊢>_
  infixl 2  _<⊢_
  infixl 2  _[_]ᴶ
  infixl 10 _[_]
  infixr 20 _⇒>_ _<⇒_
  infixl 20 _⇐>_ _<⇐_
  infixr 30 _⊗>_ _<⊗_

  open import Function                              using (id; flip; _∘_)
  open import Logic.Polarity                        using (Polarity; +; -)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  open sequent_calculus Atom        using (Type; el; _⇐_; _⊗_; _⇒_)
  open res              Atom public using (Judgement; _⊢_)
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
module res⇔resmon (Atom : Set) where

  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  module RM = resmon Atom ; open RM
  module R′ = res    Atom ; open R′
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


## Derivational Semantics

### Translation to Agda
``` hidden
module resmon→agda (Atom : Set) (⟦_⟧ᴬ : Atom → Set) where

  open import Function     using (id; flip; _∘_)
  open import Data.Product using (_×_; map; curry; uncurry)
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open resmon Atom using (RM_; _⊢_; ax; m⊗; m⇒; m⇐; r⇒⊗; r⇐⊗; r⊗⇒; r⊗⇐)
```

```
  ⟦_⟧ : Type → Set
  ⟦ el   A ⟧ = ⟦ A ⟧ᴬ
  ⟦ A ⊗  B ⟧ = ⟦ A ⟧ ×  ⟦ B ⟧
  ⟦ A ⇒  B ⟧ = ⟦ A ⟧ →  ⟦ B ⟧
  ⟦ B ⇐  A ⟧ = ⟦ A ⟧ →  ⟦ B ⟧
```

```
  [_] : ∀ {A B} → RM A ⊢ B → ⟦ A ⟧ → ⟦ B ⟧
  [ ax        ] = id
  [ m⊗   f g  ] = map [ f ] [ g ]
  [ m⇒   f g  ] = λ h → [ g ] ∘ h ∘ [ f ]
  [ m⇐   f g  ] = λ h → [ f ] ∘ h ∘ [ g ]
  [ r⇒⊗  f    ] = uncurry (flip  [ f ])
  [ r⇐⊗  f    ] = uncurry (      [ f ])
  [ r⊗⇒  f    ] = flip  (curry [ f ])
  [ r⊗⇐  f    ] =       (curry [ f ])
```

### Typing Agda
``` hidden
module resmon_typing_agda (Atom : Set) (⟦_⟧ᴬ : Atom → Set) where

  open import Function     using (id; flip; _∘_)
  open import Data.Product using (_×_; map; curry; uncurry)
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open resmon Atom using (Judgement; _⊢_)
  open resmon→agda Atom ⟦_⟧ᴬ using (⟦_⟧)
```

``` hidden
  ⟦_⟧ʲ : Judgement → Set
```
```
  ⟦ A ⊢ B ⟧ʲ = ⟦ A ⟧ → ⟦ B ⟧
```

``` hidden
  mutual
    infix 2 RM-syntax₁
    infix 2 RM-syntax₂

    RM-syntax₁ = λ A B f → RM_ (A ⊢ B) f
    RM-syntax₂ = λ A B f → RM_ (A ⊢ B) f
```

```
    syntax RM-syntax₁  A B (λ x →  f)  = f ∈ x ∶  A ⊢ B
    syntax RM-syntax₂  A B         f   = f ∈      A ⊢ B
```

```
    data RM_ : (J : Judgement) (f : ⟦ J ⟧ʲ) → Set where

      ax   : ∀ {A}
           →  x                      ∈ x   ∶  el A ⊢ el A

      m⊗   : ∀ {A B C D f g}
           →  f                      ∈        A ⊢ B
           →  g                      ∈        C ⊢ D
           →  map f g xy             ∈ xy  ∶  A ⊗ C ⊢ B ⊗ D

      m⇒   : ∀ {A B C D f g}
           →  f                      ∈        A ⊢ B
           →  g                      ∈        C ⊢ D
           →  g ∘ h ∘ f              ∈ h   ∶  B ⇒ C ⊢ A ⇒ D

      m⇐   : ∀ {A B C D f g}
           →  f                      ∈        A ⊢ B
           →  g                      ∈        C ⊢ D
           →  f ∘ h ∘ g              ∈ h   ∶  A ⇐ D ⊢ B ⇐ C

      r⇒⊗  : ∀ {A B C f}
           →  f                      ∈        B ⊢ A ⇒ C
           →  uncurry (flip  f)  xy  ∈ xy  ∶  A ⊗ B ⊢ C

      r⇐⊗  : ∀ {A B C f}
           →  f                      ∈        A ⊢ C ⇐ B
           →  uncurry        f   xy  ∈ xy  ∶  A ⊗ B ⊢ C

      r⊗⇒  : ∀ {A B C f}
           →  f                      ∈        A ⊗ B ⊢ C
           →  flip (  curry f)  x    ∈ x   ∶  B ⊢ A ⇒ C

      r⊗⇐  : ∀ {A B C f}
           →  f                      ∈        A ⊗ B ⊢ C
           →          curry f   x    ∈ x   ∶  A ⊢ C ⇐ B
```



[^prime]:  I have made it convention to label all derived and admissible rules
           with a prime. This makes it clear (without syntax highlighting) which
           rules are atomic in a system.
[^syntax]: In place of the full version (e.g. |SC_ Γ ⊢ A|) I will simply write
           |Γ ⊢ A| for judgements, and use superscripts to disambiguate when
           necessary (i.e. |Γ SC.⊢ A|).
