``` hidden
module lambek_grammar {Atom : Set} where

open import Function                              using (id; _∘_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
```

``` hidden
infixr 30 _⊗_
infixr 20 _⇒_
infixl 20 _⇐_
```

# The Lambek Calculus

- originally referred to as the 'syntactic calculus' @lambek1958

- goes back to an arithmetical notation introduced by @ajdukiewicz1935
  and @barhillel1953;

- assign types to English words by means of a set of basic types and
  the connectives {|⇒ , ⊗ , ⇐|};

- fragment of non-commutative linear logic, now called bilinear logic;

- we will discuss a fragment that drops associativity as well,
  referred to as the non-associative Lambek calculus (NL);

- arguments against associativity can be found in @moot2012 [pp 105-106]

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


```
  data SC_ : Judgement → Set where
    ax   : ∀ {A}
         →  SC · A · ⊢ A

    cut  : ∀ {Γ Δ A B}
         →  SC Δ ⊢ A → SC Γ [ · A · ] ⊢ B → SC Γ [ Δ ] ⊢ B

    ⊗L   : ∀ {Γ A B C}
         →  SC Γ [ · A · ∙ · B · ] ⊢ C → SC Γ [ · A  ⊗ B · ] ⊢ C
    ⊗R   : ∀ {Γ Δ A B}
         →  SC Γ  ⊢ A → SC Δ ⊢ B → SC Γ ∙ Δ ⊢ A ⊗ B

    ⇒L   : ∀ {Γ Δ A B C}
         →  SC Γ [ · B · ]  ⊢ C  →  SC Δ ⊢ A  →  SC Γ [ Δ ∙ · A ⇒ B · ] ⊢ C
    ⇐L   : ∀ {Γ Δ A B C}
         →  SC Γ [ · B · ]  ⊢ C  →  SC Δ ⊢ A  →  SC Γ [ · B ⇐ A · ∙ Δ ] ⊢ C

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
    \todo{Is this actually true?}


``` hidden
module Res where

  infix  1  R_
  infix  2  _⊢_
```

```
  data Judgement : Set where
    _⊢_ : Type → Type → Judgement
```


```
  data R_ : Judgement → Set where
    ax   : ∀ {A}      → R A ⊢ A
    cut  : ∀ {A B C}  → R A ⊢ B → R B ⊢ C → R A ⊢ C
    r⇒⊗  : ∀ {A B C}  → R B ⊢ A ⇒ C → R A ⊗ B ⊢ C
    r⊗⇒  : ∀ {A B C}  → R A ⊗ B ⊢ C → R B ⊢ A ⇒ C
    r⇐⊗  : ∀ {A B C}  → R A ⊢ C ⇐ B → R A ⊗ B ⊢ C
    r⊗⇐  : ∀ {A B C}  → R A ⊗ B ⊢ C → R A ⊢ C ⇐ B
```

```
  m⊗′  : ∀ {A B C D} → R A ⊢ B → R C ⊢ D → R A ⊗ C ⊢ B ⊗ D
  m⊗′  f g  = r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ (cut g (r⊗⇒ ax)))))

  m⇒′  : ∀ {A B C D} → R A ⊢ B → R C ⊢ D → R B ⇒ C ⊢ A ⇒ D
  m⇒′  f g  = r⊗⇒ (cut (r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ ax)))) g)

  m⇐′  : ∀ {A B C D} → R A ⊢ B → R C ⊢ D → R A ⇐ D ⊢ B ⇐ C
  m⇐′  f g  = r⊗⇐ (cut (r⇒⊗ (cut g (r⊗⇒ (r⇐⊗ ax)))) f)
```

We would like to be sure that the new axiomatisation for NL is
actually equally expressive.

``` hidden
module SC→R where

  module R  = Res            ; open Res
  module SC = SequentCalculus; open SequentCalculus hiding (Judgement)
```

```
  Deflate : Struct → Type
  Deflate (  Γ  ∙  Δ)  = Deflate Γ ⊗ Deflate Δ
  Deflate    ·  A  ·   = A
```

```
  cutDeflate′  : ∀ {Γ Δ Δ′ A}
               →  R Deflate Δ ⊢ Deflate Δ′
               →  R Deflate (Γ [ Δ′  ]) ⊢ A
               →  R Deflate (Γ [ Δ   ]) ⊢ A
  cutDeflate′ {Γ = []      } f g = cut f g
  cutDeflate′ {Γ = _ ∙> Γ  } f g = r⇒⊗ (cutDeflate′ {Γ = Γ} f (r⊗⇒ g))
  cutDeflate′ {Γ = Γ <∙ _  } f g = r⇐⊗ (cutDeflate′ {Γ = Γ} f (r⊗⇐ g))
```

```
  from : ∀ {Γ A} → SC Γ SC.⊢ A → R (Deflate Γ R.⊢ A)
  from    ax                  = ax
  from (  cut  {Γ = Γ}  f g)  = cutDeflate′ {Γ = Γ} (  from f)  (from g)
  from (  ⊗L   {Γ = Γ}  f)    = cutDeflate′ {Γ = Γ}    ax       (from f)
  from (  ⇒L   {Γ = Γ}  f g)  = cutDeflate′ {Γ = Γ} (r⇒⊗ (m⇒′ (from g) ax)) (from f)
  from (  ⇐L   {Γ = Γ}  f g)  = cutDeflate′ {Γ = Γ} (r⇐⊗ (m⇐′ ax (from g))) (from f)
  from (  ⊗R            f g)  = m⊗′  (from f) (from g)
  from (  ⇒R            f)    = r⊗⇒  (from f)
  from (  ⇐R            f)    = r⊗⇐  (from f)
```

```
  to : ∀ {A B} → R A R.⊢ B → SC · A · SC.⊢ B
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

  open Res using (Judgement; _⊢_)
```


```
  data RM_ : Judgement → Set where
    ax   : ∀ {A}       → RM el A ⊢ el A
    m⊗   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM A ⊗ C ⊢ B ⊗ D
    m⇒   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM B ⇒ C ⊢ A ⇒ D
    m⇐   : ∀ {A B C D} → RM A ⊢ B     → RM C ⊢ D     → RM A ⇐ D ⊢ B ⇐ C
    r⇒⊗  : ∀ {A B C}   → RM B ⊢ A ⇒ C → RM A ⊗ B ⊢ C
    r⊗⇒  : ∀ {A B C}   → RM A ⊗ B ⊢ C → RM B ⊢ A ⇒ C
    r⇐⊗  : ∀ {A B C}   → RM A ⊢ C ⇐ B → RM A ⊗ B ⊢ C
    r⊗⇐  : ∀ {A B C}   → RM A ⊗ B ⊢ C → RM A ⊢ C ⇐ B
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

```
  data Polarity : Set where + - : Polarity
```

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
      view ([] <⊢ ._)        (r⊗⇒ f)    = go ((_ ⊗> []) <⊢ _)        f  r⊗⇒
      view ([] <⊢ ._)        (r⊗⇐ f)    = go (([] <⊗ _) <⊢ _)        f  r⊗⇐
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = go (B <⊢ _)                g  (m⊗ f)
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = go (B <⊢ _)                f  r⇒⊗
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = go ((_ ⊗> (A ⊗> B)) <⊢ _)  f  r⊗⇒
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = go (_ ⊢> (_ ⇐> B))         f  r⇐⊗
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = go (((A ⊗> B) <⊗ _) <⊢ _)  f  r⊗⇐
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = go (A <⊢ _)                f  (flip m⊗ g)
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = go (_ ⊢> (A <⇒ _))         f  r⇒⊗
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = go ((_ ⊗> (A <⊗ B)) <⊢ _)  f  r⊗⇒
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = go (A <⊢ _)                f  r⇐⊗
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = go (((A <⊗ B) <⊗ _) <⊢ _)  f  r⊗⇐
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = go (_ ⊢> B)                g  (m⇒ f)
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A ⇒> B)))  f  r⇒⊗
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = go (_ ⊢> B)                f  r⊗⇒
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = go (_ ⊢> ((A ⇒> B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = go (B <⊢ _)                g  (m⇐ f)
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A ⇐> B)))  f  r⇒⊗
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = go (_ ⊢> ((A ⇐> B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = go ((_ ⊗> B) <⊢ _)         f  r⊗⇐
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = go (A <⊢ _)                f  (flip m⇒ g)
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A <⇒ B)))  f  r⇒⊗
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = go ((A <⊗ _) <⊢ _)         f  r⊗⇒
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = go (_ ⊢> ((A <⇒ B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = go (_ ⊢> A)                f  (flip m⇐ g)
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A <⇐ B)))  f  r⇒⊗
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = go (_ ⊢> ((A <⇐ B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = go (_ ⊢> A)                f  r⊗⇐

      go : ∀ {B}
         → ( I : Contextᴶ + ) (f : RM I [ el B ]ᴶ) { J : Contextᴶ + } (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) → Origin J (g f)
      go I f {J} g with view I f; ... | origin f′ pr rewrite pr = origin (g ∘ f′) refl
```
```
  module ⊗ where

    data Origin {B C} ( J : Contextᴶ - ) (f : RM J [ B ⊗ C ]ᴶ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : RM E ⊢ B)
                 →  (h₂  : RM F ⊢ C)
                 →  (f′  : ∀ {G} → RM E ⊗ F ⊢ G → RM J [ G ]ᴶ)
                 →  (pr  : f ≡ f′ (m⊗ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextᴶ - ) (f : RM J [ B ⊗ C ]ᴶ) → Origin J f
      view (._ ⊢> [])        (m⊗   f g)  =  origin f g id refl
      view (._ ⊢> [])        (r⇒⊗  f)    =  wrap {_ ⊢> (_ ⇒> [])      }         r⇒⊗    f
      view (._ ⊢> [])        (r⇐⊗  f)    =  wrap {_ ⊢> ([] <⇐ _)      }         r⇐⊗    f
      view ((_ ⊗> A) <⊢ ._)  (m⊗   f g)  =  wrap {A <⊢ _              }  (      m⊗ f)  g
      view ((_ ⊗> A) <⊢ ._)  (r⇒⊗  f)    =  wrap {A <⊢ _              }         r⇒⊗    f
      view ((_ ⊗> A) <⊢ ._)  (r⊗⇒  f)    =  wrap {(_ ⊗> (_ ⊗> A)) <⊢ _}         r⊗⇒    f
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

      wrap : ∀ { I : Contextᴶ - } { J : Contextᴶ - } {B C}
           →  (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) (f : RM I [ B ⊗ C ]ᴶ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl
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
      view ([] <⊢ ._)        (r⊗⇒ f)    = go ((_ ⊗> []) <⊢ _)        f  r⊗⇒
      view ([] <⊢ ._)        (r⊗⇐ f)    = go (([] <⊗ _) <⊢ _)        f  r⊗⇐
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = go (B <⊢ _)                g  (m⊗ f)
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = go (B <⊢ _)                f  r⇒⊗
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = go ((_ ⊗> (A ⊗> B)) <⊢ _)  f  r⊗⇒
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = go (_ ⊢> (_ ⇐> B))         f  r⇐⊗
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = go (((A ⊗> B) <⊗ _) <⊢ _)  f  r⊗⇐
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = go (A <⊢ _)                f  (flip m⊗ g)
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = go (_ ⊢> (A <⇒ _))         f  r⇒⊗
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = go ((_ ⊗> (A <⊗ B)) <⊢ _)  f  r⊗⇒
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = go (A <⊢ _)                f  r⇐⊗
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = go (((A <⊗ B) <⊗ _) <⊢ _)  f  r⊗⇐
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = go (_ ⊢> B)                g  (m⇒ f)
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A ⇒> B)))  f  r⇒⊗
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = go (_ ⊢> B)                f  r⊗⇒
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = go (_ ⊢> ((A ⇒> B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = go (B <⊢ _)                g  (m⇐ f)
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A ⇐> B)))  f  r⇒⊗
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = go (_ ⊢> ((A ⇐> B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = go ((_ ⊗> B) <⊢ _)         f  r⊗⇐
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = go (A <⊢ _)                f  (flip m⇒ g)
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A <⇒ B)))  f  r⇒⊗
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = go ((A <⊗ _) <⊢ _)         f  r⊗⇒
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = go (_ ⊢> ((A <⇒ B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = go (_ ⊢> A)                f  (flip m⇐ g)
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A <⇐ B)))  f  r⇒⊗
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = go (_ ⊢> ((A <⇐ B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = go (_ ⊢> A)                f  r⊗⇐

      go : ∀ {B C}
         → ( I : Contextᴶ + ) (f : RM I [ B ⇒ C ]ᴶ) { J : Contextᴶ + } (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) → Origin J (g f)
      go I f {J} g with view I f; ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl
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
      view ([] <⊢ ._)        (r⊗⇒ f)    = go ((_ ⊗> []) <⊢ _)        f  r⊗⇒
      view ([] <⊢ ._)        (r⊗⇐ f)    = go (([] <⊗ _) <⊢ _)        f  r⊗⇐
      view ((A ⊗> B) <⊢ ._)  (m⊗  f g)  = go (B <⊢ _)                g  (m⊗ f)
      view ((A ⊗> B) <⊢ ._)  (r⇒⊗ f)    = go (B <⊢ _)                f  r⇒⊗
      view ((A ⊗> B) <⊢ ._)  (r⊗⇒ f)    = go ((_ ⊗> (A ⊗> B)) <⊢ _)  f  r⊗⇒
      view ((A ⊗> B) <⊢ ._)  (r⇐⊗ f)    = go (_ ⊢> (_ ⇐> B))         f  r⇐⊗
      view ((A ⊗> B) <⊢ ._)  (r⊗⇐ f)    = go (((A ⊗> B) <⊗ _) <⊢ _)  f  r⊗⇐
      view ((A <⊗ B) <⊢ ._)  (m⊗  f g)  = go (A <⊢ _)                f  (flip m⊗ g)
      view ((A <⊗ B) <⊢ ._)  (r⇒⊗ f)    = go (_ ⊢> (A <⇒ _))         f  r⇒⊗
      view ((A <⊗ B) <⊢ ._)  (r⊗⇒ f)    = go ((_ ⊗> (A <⊗ B)) <⊢ _)  f  r⊗⇒
      view ((A <⊗ B) <⊢ ._)  (r⇐⊗ f)    = go (A <⊢ _)                f  r⇐⊗
      view ((A <⊗ B) <⊢ ._)  (r⊗⇐ f)    = go (((A <⊗ B) <⊗ _) <⊢ _)  f  r⊗⇐
      view (._ ⊢> (A ⇒> B))  (m⇒  f g)  = go (_ ⊢> B)                g  (m⇒ f)
      view (._ ⊢> (A ⇒> B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A ⇒> B)))  f  r⇒⊗
      view (._ ⊢> (A ⇒> B))  (r⊗⇒ f)    = go (_ ⊢> B)                f  r⊗⇒
      view (._ ⊢> (A ⇒> B))  (r⇐⊗ f)    = go (_ ⊢> ((A ⇒> B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A ⇐> B))  (m⇐  f g)  = go (B <⊢ _)                g  (m⇐ f)
      view (._ ⊢> (A ⇐> B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A ⇐> B)))  f  r⇒⊗
      view (._ ⊢> (A ⇐> B))  (r⇐⊗ f)    = go (_ ⊢> ((A ⇐> B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A ⇐> B))  (r⊗⇐ f)    = go ((_ ⊗> B) <⊢ _)         f  r⊗⇐
      view (._ ⊢> (A <⇒ B))  (m⇒  f g)  = go (A <⊢ _)                f  (flip m⇒ g)
      view (._ ⊢> (A <⇒ B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A <⇒ B)))  f  r⇒⊗
      view (._ ⊢> (A <⇒ B))  (r⊗⇒ f)    = go ((A <⊗ _) <⊢ _)         f  r⊗⇒
      view (._ ⊢> (A <⇒ B))  (r⇐⊗ f)    = go (_ ⊢> ((A <⇒ B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A <⇐ B))  (m⇐  f g)  = go (_ ⊢> A)                f  (flip m⇐ g)
      view (._ ⊢> (A <⇐ B))  (r⇒⊗ f)    = go (_ ⊢> (_ ⇒> (A <⇐ B)))  f  r⇒⊗
      view (._ ⊢> (A <⇐ B))  (r⇐⊗ f)    = go (_ ⊢> ((A <⇐ B) <⇐ _))  f  r⇐⊗
      view (._ ⊢> (A <⇐ B))  (r⊗⇐ f)    = go (_ ⊢> A)                f  r⊗⇐

      go : ∀ {B C}
         → ( I : Contextᴶ + ) (f : RM I [ B ⇐ C ]ᴶ) { J : Contextᴶ + } (g : ∀ {G} → RM I [ G ]ᴶ → RM J [ G ]ᴶ) → Origin J (g f)
      go I f {J} g with view I f; ... | origin h₁ h₂ f′ pr rewrite pr = origin h₁ h₂ (g ∘ f′) refl
```

[^prime]: I have made it convention to label all derived and admissible rules
          with a prime. This makes it clear (without syntax highlighting) which
          rules are atomic in a system.
