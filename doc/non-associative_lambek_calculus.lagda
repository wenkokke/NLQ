# Non-associative Lambek Calculus
``` hidden
module non-associative_lambek_calculus where
```

In this section we will discuss the non-associative Lambek calculus
(NL), which forms the basis of most categorial grammar and
type-logical grammar systems.

We will set out to discuss the two systems introced by
@lambek1961. The first of these two is a sequent calculus, which was
introduced in order to obtain a proof of cut elimination, and all the
associated corollaries. The second system is a combinator calculus,
which is considerably simpler and easier to compute with.
After these two systems, we will discuss a cut-free combinator
calculus, as discovered by @moortgat1999. To round this section, we
will discuss a direct translation of the cut-free system into Agda,
which we will use for our semantic interpretation, thereby obtaining a
complete type-logical grammar. Further additions to the
non-associative Lambek calculus will be discussed in section
\ref{display-calculus}.


## Sequent Calculus

In this section we will discuss the sequent calculus for the
non-associative Lambek calculus, due to @lambek1961. This calculus was
set up in order to obtain a cut-elimination procedure à la Gentzen.
For NL---as opposed to the associative Lambek calculus L---this was
not immediately obvious, and it was only proven in TODO @kandulsky.
However, the discovery of a cut-elimination procedure for the
combinator calculus has made this role of the sequent calculus
obsolete. Our reason for nevertheless discussing the sequent calculus
is as follows: we would like to have the opportunity to discuss a
calculus and its encoding in Agda in great detail, before delving into
the remainder of this thesis. Therefore, should you feel familiar with
the style of encoding used in this thesis, you can skip this section
altogether, and continue in section \ref{the-system-with-residuation-r}.

The formulas for the base system NL are built up over a set of atomic
formulas and three connectives. Usually these atomic formulas are at
least `n`, `np` and `s` for *noun*, *noun phrase* and *sentence*, but
we would not want to exclude others such as `pp` for *prepositional
phrase* or `inf` for *infinitive*. In order to avoid committing to a
certain set of atomic formulas and side-step the debate on which
formulas should be atomic, we will simply assume there is a some data
type representing our atomic formulas. This will be reflected in our
module header as follows:

```
module sequent_calculus (Atom : Set) where
```
``` hidden
  infixr 1 SC_
  infix  2 _⊢_
  infix  2 _⊢SC_
  infixl 3 _[_]
  infix  4 _∙_ _∙>_ _<∙_
  infixr 30 _⊗_
  infixr 20 _⇒_
  infixl 20 _⇐_
```

Note that the type `Set` here is the type of types from type theory,
and is not related to the sets from mathematics.

Our formulas can easily be described as a data type, injecting our
atomic formulas by means of the constructor el, and adding the
connectives from NL as binary constructors. For these connectives, we
have a product (`⊗`) and *two* implications (`⇒` and `⇐`).
Note that, in Agda, we can use underscores in definitions to denote
argument positions. This means that $\_⊗\_$ below defines an infix,
binary connective:

```
  data Type : Set where
    el   : Atom  → Type
    _⊗_  : Type  → Type → Type
    _⇒_  : Type  → Type → Type
    _⇐_  : Type  → Type → Type
```

As in intuitionistic logic, the antecedent is a *structure* of
formulas. However, while they appear similar, the structures of NL are
binary trees as opposed to sets.

```
  data Struct : Set where
    ·_·  : Type    → Struct
    _∙_  : Struct  → Struct → Struct
```

In addition, the rules of our sequent calculus can often apply
anywhere in the structure. In order to deal with this, we will define
the concept of a 'context', which is a structure with exactly one hole
(written []) in it. The other two constructors for contexts are
variations on the structure's $\_,\_$, annotated with a small triangle
which points towards where the hole is:

```
  data Context : Set where
    []    : Context
    _∙>_  : Struct   → Context  → Context
    _<∙_  : Context  → Struct   → Context
```

In order to give a meaningful interpretation to these context, we
define the action of 'plugging', or inserting a structure into the
hole in a context:

```
  _[_] : Context → Struct → Struct
  []       [ Δ ] = Δ
  Γ ∙> Γ′  [ Δ ] = Γ ∙ (Γ′ [ Δ ])
  Γ <∙ Γ′  [ Δ ] = (Γ [ Δ ]) ∙ Γ′
```

Lastly, we need to define judgements. While the term 'judgement'
usually refers to a statement *and a proof*, we shall take judgement
to refer to the syntactic statement alone. The reason for this is that
it is incredibly useful to be able to talk about 'judgements' without
having to associate these with proof. And as we will see later, the
concept of a 'judgement context' or a judgement with a variable in the
ante- or succedent is also incredibly useful. For the sequent calculus
we are about to implement the judgements consist of a structure in the
antecedent and a single formula in the succedent:

```
  data Sequent : Set where
    _⊢_ : Struct → Type → Sequent
```

With all this syntactic boilerplate out of the way, we will now define
the structure of SC (for sequent calculus).
Note that while we would have to write $SC\;\Gamma\;⊢\;A$ to denote the type
of a term in SC, we will allow ourselves some freedom in typesetting
and simply write $\Gamma\;\vdash\;A$. In the case where it is unclear
which system we are discussing, we will use superscripts to
disambiguate and write e.g. $\Gamma\;\vdash^{\textsc{SC}}\;A$:


``` hidden
  mutual
    _⊢SC_ : Struct → Type → Set
    Γ ⊢SC B = SC Γ ⊢ B

    data SC_ : Sequent → Set where

      ax   : ∀ {A}
           →  · A · ⊢SC A

      cut  : ∀ {Γ Δ A B}
           →  Δ ⊢SC A → Γ [ · A · ] ⊢SC B → Γ [ Δ ] ⊢SC B

      ⊗L   : ∀ {Γ A B C}
           →  Γ [ · A · ∙ · B · ] ⊢SC C → Γ [ · A  ⊗ B · ] ⊢SC C
      ⇒L   : ∀ {Γ Δ A B C}
           →  Γ [ · B · ]  ⊢SC C  →  Δ ⊢SC A  →  Γ [ Δ ∙ · A ⇒ B · ] ⊢SC C
      ⇐L   : ∀ {Γ Δ A B C}
           →  Γ [ · B · ]  ⊢SC C  →  Δ ⊢SC A  →  Γ [ · B ⇐ A · ∙ Δ ] ⊢SC C

      ⊗R   : ∀ {Γ Δ A B}
           →  Γ  ⊢SC A → Δ ⊢SC B → Γ ∙ Δ ⊢SC A ⊗ B
      ⇒R   : ∀ {Γ A B}
           →  · A · ∙ Γ  ⊢SC B  →  Γ  ⊢SC A ⇒ B
      ⇐R   : ∀ {Γ A B}
           →  Γ ∙ · A ·  ⊢SC B  →  Γ  ⊢SC B ⇐ A
```

[compute](Example/System/NL/SC.agda "asMathPar (quote NL_)")

There are reasons in favour of and against the use of contexts. One
reason *for* the use of contexts is that it makes your proofs much
shorter[^short], as we will see below. However, the reasons against using
contexts are that:

  1. it puts the plugging function `_[_]` in the return type of your
     data type definition, which usually leads to trouble with unification,
     and theories which are much more difficult to prove with [@mcbride2014,
     pp. 298-299]. The reason for this is that the term $\Gamma\;[A]$,
     given an unknown $\Gamma$ does not reduce, and therefore Agda
     cannot pattern match on a term for which the structure is not
     known;

  2. it requires you to annotate your proofs with the contexts under
     which each rule is applied;

  3. it is hard to reduce spurious ambiguity in a sequent calculus
     which uses contexts, as the restrictions on the order in which
     the rules can be applied have to be put on the contexts under
     which they are applied;

Because of this, we would rather have a system which does not use
contexts in its rules. We will define such a system in the next
section.



## The system with residuation R
<!-- Getting contexts out of the way -->
``` hidden
module res (Atom : Set) where

  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  infix  1  R_
  infix  2  _⊢_
  infix  2  _⊢R_
```
In his paper, @lambek1961 also defines a combinator calculus, which we
will refer to as R for residuation. The system itself is incredibly
simple: it features reflexivity, transitivity, and two bidirectional
residuation rules. Because this system does away with 'application
under a context' there is also no need for structures, and we can make
the system a direct binary relation on formulas:
```
  data Sequent : Set where
    _⊢_ : Type → Type → Sequent
```
The system itself is as follows:
``` hidden
  mutual
    _⊢R_ : Type → Type → Set
    A ⊢R B = R A ⊢ B

    data R_ : Sequent → Set where
      ax   : ∀ {A}      → A ⊢R A

      cut  : ∀ {A B C}  → A ⊢R B → B ⊢R C → A ⊢R C

      r⇒⊗  : ∀ {A B C}  → B ⊢R A ⇒ C  → A ⊗ B ⊢R C
      r⊗⇒  : ∀ {A B C}  → A ⊗ B ⊢R C  → B ⊢R A ⇒ C
      r⇐⊗  : ∀ {A B C}  → A ⊢R C ⇐ B  → A ⊗ B ⊢R C
      r⊗⇐  : ∀ {A B C}  → A ⊗ B ⊢R C  → A ⊢R C ⇐ B
```

[compute](Example/System/NL/Res.agda "asMathPar (quote NL_)")

The idea behind the residuation rules is that, where we used to apply
a rule under a context, they will allow us to take the formulas apart.
This means that an application of a rule `f` under a context `_ ⊗>
(([] <⊗ _) <⊗ _)` now becomes a sequence of three applications of
residuation, a cut with `f`, and three more applications of
residuation.


### Equivalence between sequent calculus and R
``` hidden
module sequent_calculus⇔res (Atom : Set) where

  module R = res              Atom ; open R hiding (Sequent)
  module SC = sequent_calculus Atom ; open SC hiding (Sequent)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
```

We would like to be sure that the new axiomatisation for NL is
actually equally expressive. One direction of this proof, converting
from the residuated system to the sequent calculus, is almost
trivial. The residuation rules translate to sequences of left or right
rules, depending on the direction of the residuation and the involved
connectives. The cut rules simply translates to its more expressive
equivalent:

```
  to : ∀ {A B} → A R.⊢R B → · A · SC.⊢SC B
  to    ax           = ax
  to (  cut  f g  )  = cut  {Γ = []} (to f) (to g)
  to (  r⇒⊗  f    )  = ⊗L   {Γ = []} (cut {Γ = _ ∙> []} (to f) (⇒L {Γ = []} ax ax))
  to (  r⇐⊗  f    )  = ⊗L   {Γ = []} (cut {Γ = [] <∙ _} (to f) (⇐L {Γ = []} ax ax))
  to (  r⊗⇒  f    )  = ⇒R (cut {Γ = []} (⊗R ax ax) (to f))
  to (  r⊗⇐  f    )  = ⇐R (cut {Γ = []} (⊗R ax ax) (to f))
```

However, since the sequent calculus uses structures as its antecedent,
the other direction is much more involved, as we need a way to convert
structures to formulas. Fortunately, we have already seen that the
structural operator `∙` is simply a restricted version of the product
`⊗`, so we can convert it to this:

```
  ⌊_⌋ : Struct → Type
  ⌊ · A ·  ⌋  = A
  ⌊ Γ ∙ Δ  ⌋  = ⌊ Γ ⌋ ⊗ ⌊ Δ ⌋
```

The second problem is the problem of applying rules under contexts. In
the previous section, we hinted at a solution which used residuation
to move the context out of the way. The precise definition of this is
as follows:

```
  cutIn′  : ∀ {Γ Δ Δ′ A}
          → ⌊ Δ ⌋ ⊢R ⌊ Δ′ ⌋ → ⌊ Γ [ Δ′  ] ⌋ ⊢R A → ⌊ Γ [ Δ   ] ⌋ ⊢R A
  cutIn′ {  Γ = []      } f g = cut f g
  cutIn′ {  Γ = _ ∙> Γ  } f g = r⇒⊗ (cutIn′ {Γ = Γ} f (r⊗⇒ g))
  cutIn′ {  Γ = Γ <∙ _  } f g = r⇐⊗ (cutIn′ {Γ = Γ} f (r⊗⇐ g))
```

Last, we need to prove a lemma which states that in translating `⊗L`
we don't need to do anything, as the flattening function `⌊_⌋` will
make both sides equal. This is provable by simple induction over the
structure of the context `Γ`:

```
  lemma-⌊_⌋  : ∀ Γ → ∀ {A B} → ⌊ Γ [ · A ⊗ B · ] ⌋ ≡ ⌊ Γ [ · A · ∙ · B · ] ⌋
  lemma-⌊_⌋  []       {A} {B} = refl
  lemma-⌊_⌋  (_ ∙> Γ) {A} {B} rewrite lemma-⌊_⌋ Γ {A} {B} = refl
  lemma-⌊_⌋  (Γ <∙ _) {A} {B} rewrite lemma-⌊_⌋ Γ {A} {B} = refl
```

Using these three functions, the solution becomes quite simple. The cut
rule translates to the lemma `cutIn′`, the `⊗L` translates to the
identity, and the remaining rules translate to some combination of the
residuation rules with `cut` and `cutIn′`:

```
  from : ∀ {Γ A} → Γ SC.⊢SC A → ⌊ Γ ⌋ R.⊢R A
  from    ax                          = ax
  from (  cut  {Γ = Γ}  f g        )  = cutIn′ {Γ = Γ} (from f)  (from g)
  from (  ⊗L   {Γ = Γ}  {A} {B} f  )  rewrite lemma-⌊_⌋ Γ {A} {B} = from f
  from (  ⊗R            f g        )  = r⇐⊗ (cut (from f) (r⊗⇐ (r⇒⊗ (cut (from g) (r⊗⇒ ax)))))
  from (  ⇒L   {Γ = Γ}  f g        )  = cutIn′ {Γ = Γ} (r⇐⊗ (cut (from g) (r⊗⇐ (r⇒⊗ ax)))) (from f)
  from (  ⇐L   {Γ = Γ}  f g        )  = cutIn′ {Γ = Γ} (r⇒⊗ (cut (from g) (r⊗⇒ (r⇐⊗ ax)))) (from f)
  from (  ⇒R            f          )  = r⊗⇒ (from f)
  from (  ⇐R            f          )  = r⊗⇐ (from f)
```

Now that we have eliminated the complexity introduced by contexts from
our system, we can have a look at the other unwanted complexities
still present. The most important of these are the `ax` and the `cut`
rules, which unnecessarily complicate proof search. We will have a
closer look at these rules in the next section.


## The cut-free system RM

The rules `ax` and the `cut` unnecessarily complicate proof
search. The reasons for this are as follows:

  - In the case of `ax`, the problem is that it can accept any
    formula. Therefore, there are two proofs for e.g. `A ⊗ B ⊢ A ⊗
    B`. The shortest of these is simply `ax`. However, the other proof
    is `r⇐⊗ (cut ax (r⊗⇐ (r⇒⊗ (cut ax (r⊗⇒ ax)))))`.

  - In the case of `cut`, the problem is that during proof search it
    can always be applied to the current goal, as it produces a
    sequent of type `A ⊢ C` for any `A` and `C`. Additionally, it
    introduces a new formula `B`.

We could write a procedure which takes a proof in R and eliminates all
non-atomic uses of `ax`---this procedure is commonly referred to as
'identity expansion'. For `cut` we can engineer a similar procedure,
which eliminates all non-atomic uses of `cut`. However, while it is
obvious what an atomic use of `ax` is---an application of `ax` to an
atomic formula---it unfortunately is not immediately clear what
constitutes a non-atomic `cut`. A proof due to @moortgat1999 shows
that the following three derivable rules are good candidates. That is
to say, all applications of `cut` can be reduced to applications of
just these three rules, using a procedure that is commonly referred to
as 'cut elimination':

```
  m⊗′  : ∀ {A B C D} → A ⊢R B → C ⊢R D → A ⊗ C ⊢R B ⊗ D
  m⊗′  f g  = r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ (cut g (r⊗⇒ ax)))))

  m⇒′  : ∀ {A B C D} → A ⊢R B → C ⊢R D → B ⇒ C ⊢R A ⇒ D
  m⇒′  f g  = r⊗⇒ (cut (r⇐⊗ (cut f (r⊗⇐ (r⇒⊗ ax)))) g)

  m⇐′  : ∀ {A B C D} → A ⊢R B → C ⊢R D → A ⇐ D ⊢R B ⇐ C
  m⇐′  f g  = r⊗⇐ (cut (r⇒⊗ (cut g (r⊗⇒ (r⇐⊗ ax)))) f)
```

However, there is some problem with simply procedurally reducing all
applications of `ax` and `cut` to their atomic forms.
Both of these problems are resolved in the system RM (for residuation
and monotonicity), by taking the above rules as primitive and removing
the `cut` rule:

``` hidden
module resmon (Atom : Set) where

  infix  1  RM_
  infix  2  _⊢RM_
  infixl 2  _⊢>_
  infixl 2  _<⊢_
  infixl 2  _[_]ʲ
  infixl 10 _[_]
  infixr 20 _⇒>_ _<⇒_
  infixl 20 _⇐>_ _<⇐_
  infixr 30 _⊗>_ _<⊗_

  open import Function                              using (id; flip; _∘_)
  open import Logic.Polarity                        using (Polarity; +; -)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  open sequent_calculus Atom                        using (Type; el; _⇐_; _⊗_; _⇒_)
  open res              Atom public                 using (Sequent; _⊢_)
```
``` hidden
  mutual
    _⊢RM_ : Type → Type → Set
    A ⊢RM B = RM A ⊢ B

    data RM_ : Sequent → Set where

      ax   : ∀ {A}       → el A ⊢RM el A

      m⊗   : ∀ {A B C D} → A ⊢RM B  → C ⊢RM D  → A ⊗ C ⊢RM B ⊗ D
      m⇒   : ∀ {A B C D} → A ⊢RM B  → C ⊢RM D  → B ⇒ C ⊢RM A ⇒ D
      m⇐   : ∀ {A B C D} → A ⊢RM B  → C ⊢RM D  → A ⇐ D ⊢RM B ⇐ C

      r⇒⊗  : ∀ {A B C}   → B ⊢RM A ⇒ C  → A ⊗ B ⊢RM C
      r⊗⇒  : ∀ {A B C}   → A ⊗ B ⊢RM C  → B ⊢RM A ⇒ C
      r⇐⊗  : ∀ {A B C}   → A ⊢RM C ⇐ B  → A ⊗ B ⊢RM C
      r⊗⇐  : ∀ {A B C}   → A ⊗ B ⊢RM C  → A ⊢RM C ⇐ B
```

[compute](Example/System/NL/ResMon.agda "asMathPar (quote NL_)")

Using these monotonicity rules we can easily recover the full axiom
rule as `ax′` below:

```
  ax′ : ∀ {A} → A ⊢RM A
  ax′ {A =  el    A  } = ax
  ax′ {A =  A  ⊗  B  } = m⊗  ax′ ax′
  ax′ {A =  A  ⇐  B  } = m⇐  ax′ ax′
  ax′ {A =  A  ⇒  B  } = m⇒  ax′ ax′
```

Showing that `cut′` is an admissible rule in this system is
slightly more involved.

\par\ExecuteMetaData[other.tex]{Polarity}

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
  B ⇒> C  [ A ] = B ⇒ (C [ A ])
  B ⇐> C  [ A ] = B ⇐ (C [ A ])
  C <⊗ B  [ A ] = (C [ A ]) ⊗ B
  C <⇒ B  [ A ] = (C [ A ]) ⇒ B
  C <⇐ B  [ A ] = (C [ A ]) ⇐ B
```

```
  data Contextʲ (p : Polarity) : Set where
    _<⊢_  : Context p +  → Type         → Contextʲ p
    _⊢>_  : Type         → Context p -  → Contextʲ p
```

```
  _[_]ʲ : ∀ {p} → Contextʲ p → Type → Sequent
  A <⊢ B [ C ]ʲ = A [ C ] ⊢ B
  A ⊢> B [ C ]ʲ = A ⊢ B [ C ]
```

``` hidden
  module el where

    data Origin {B} ( J : Contextʲ + ) (f : RM J [ el B ]ʲ) : Set where
         origin  : (f′ : ∀ {G} → G ⊢RM el B → RM J [ G ]ʲ)
                 → (pr : f ≡ f′ ax)
                 → Origin J f

    mutual
      view : ∀ {B} ( J : Contextʲ + ) (f : RM J [ el B ]ʲ) → Origin J f
      view ([] <⊢ ._)           ax          = origin id refl
      view ((A <⊗ _) <⊢ ._)  (  m⊗   f g  ) = wrap { (A <⊢ _)        }  (flip  m⊗ g)  f
      view ((_ ⊗> B) <⊢ ._)  (  m⊗   f g  ) = wrap { (B <⊢ _)        }  (      m⊗ f)  g
      view (._ ⊢> (_ ⇒> B))  (  m⇒   f g  ) = wrap { (_ ⊢> B)        }  (      m⇒ f)  g
      view (._ ⊢> (A <⇒ _))  (  m⇒   f g  ) = wrap { (A <⊢ _)        }  (flip  m⇒ g)  f
      view (._ ⊢> (_ ⇐> B))  (  m⇐   f g  ) = wrap { (B <⊢ _)        }  (      m⇐ f)  g
      view (._ ⊢> (A <⇐ _))  (  m⇐   f g  ) = wrap { (_ ⊢> A)        }  (flip  m⇐ g)  f
      view (A <⊢ ._)         (  r⊗⇒  f    ) = wrap { ((_ ⊗> A) <⊢ _) }         r⊗⇒    f
      view (._ ⊢> (_ ⇒> B))  (  r⊗⇒  f    ) = wrap { (_ ⊢> B)        }         r⊗⇒    f
      view (._ ⊢> (A <⇒ _))  (  r⊗⇒  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇒    f
      view ((_ ⊗> B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (B <⊢ _)        }         r⇒⊗    f
      view ((A <⊗ _) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (_ ⊢> (A <⇒ _)) }         r⇒⊗    f
      view (._ ⊢> B)         (  r⇒⊗  f    ) = wrap { (_ ⊢> (_ ⇒> B)) }         r⇒⊗    f
      view (A <⊢ ._)         (  r⊗⇐  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (_ ⇐> B))  (  r⊗⇐  f    ) = wrap { ((_ ⊗> B) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A <⇐ _))  (  r⊗⇐  f    ) = wrap { (_ ⊢> A)        }         r⊗⇐    f
      view ((_ ⊗> B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (_ ⊢> (_ ⇐> B)) }         r⇐⊗    f
      view ((A <⊗ _) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (A <⊢ _)        }         r⇐⊗    f
      view (._ ⊢> B)         (  r⇐⊗  f    ) = wrap { (_ ⊢> (B <⇐ _)) }         r⇐⊗    f

      wrap : ∀ { I : Contextʲ + } { J : Contextʲ + } {B}
           →   (g : ∀ {G} → RM I [ G ]ʲ → RM J [ G ]ʲ) (f : RM I [ el B ]ʲ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin f′ pr = origin (g ∘ f′) (cong g pr)
```
```
  module ⊗ where
```
```
    data Origin {B C} ( J : Contextʲ - ) (f : RM J [ B ⊗ C ]ʲ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : E ⊢RM B)
                 →  (h₂  : F ⊢RM C)
                 →  (f′  : ∀ {G} → E ⊗ F ⊢RM G → RM J [ G ]ʲ)
                 →  (pr  : f ≡ f′ (m⊗ h₁ h₂))
                 →  Origin J f
```
``` hidden
    mutual
```
``` partial
      view : ∀ {B C} ( J : Contextʲ - ) (f : RM J [ B ⊗ C ]ʲ) → Origin J f
      view (._ ⊢> [])        (  m⊗   f g  ) = origin f g id refl
      view ((A <⊗ B) <⊢ ._)  (  m⊗   f g  ) = wrap { (A <⊢ _)        }  (flip  m⊗ g)  f
      view ((A ⊗> B) <⊢ ._)  (  m⊗   f g  ) = wrap { (B <⊢ _)        }  (      m⊗ f)  g
      view (._ ⊢> (A ⇒> B))  (  m⇒   f g  ) = wrap { (_ ⊢> B)        }  (      m⇒ f)  g
      view (._ ⊢> (A <⇒ B))  (  m⇒   f g  ) = wrap { (A <⊢ _)        }  (flip  m⇒ g)  f
      view (._ ⊢> (A ⇐> B))  (  m⇐   f g  ) = wrap { (B <⊢ _)        }  (      m⇐ f)  g
      view (._ ⊢> (A <⇐ B))  (  m⇐   f g  ) = wrap { (_ ⊢> A)        }  (flip  m⇐ g)  f
      view (A <⊢ ._)         (  r⊗⇒  f    ) = wrap { ((_ ⊗> A) <⊢ _) }         r⊗⇒    f
      view (._ ⊢> (A ⇒> B))  (  r⊗⇒  f    ) = wrap { (_ ⊢> B)        }         r⊗⇒    f
      view (._ ⊢> (A <⇒ B))  (  r⊗⇒  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇒    f
      view ((A ⊗> B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (B <⊢ _)        }         r⇒⊗    f
      view ((A <⊗ B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (_ ⊢> (A <⇒ _)) }         r⇒⊗    f
      view (._ ⊢> B)         (  r⇒⊗  f    ) = wrap { (_ ⊢> (_ ⇒> B)) }         r⇒⊗    f
      view (A <⊢ ._)         (  r⊗⇐  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A ⇐> B))  (  r⊗⇐  f    ) = wrap { ((_ ⊗> B) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A <⇐ B))  (  r⊗⇐  f    ) = wrap { (_ ⊢> A)        }         r⊗⇐    f
      view ((A ⊗> B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (_ ⊢> (_ ⇐> B)) }         r⇐⊗    f
      view ((A <⊗ B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (A <⊢ _)        }         r⇐⊗    f
      view (._ ⊢> B)         (  r⇐⊗  f    ) = wrap { (_ ⊢> (B <⇐ _)) }         r⇐⊗    f
```
```
      wrap : ∀ { I : Contextʲ - } { J : Contextʲ - } {B C}
           →  (g : ∀ {G} → RM I [ G ]ʲ → RM J [ G ]ʲ) (f : RM I [ B ⊗ C ]ʲ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
```
``` hidden
  module ⇒ where

    data Origin {B C} ( J : Contextʲ + ) (f : RM J [ B ⇒ C ]ʲ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : E ⊢RM B)
                 →  (h₂  : C ⊢RM F)
                 →  (f′  : ∀ {G} → G ⊢RM E ⇒ F → RM J [ G ]ʲ)
                 →  (pr  : f ≡ f′ (m⇒ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextʲ + ) (f : RM J [ B ⇒ C ]ʲ) → Origin J f
      view ([] <⊢ ._)        (  m⇒   f g  ) = origin f g id refl
      view ((A <⊗ B) <⊢ ._)  (  m⊗   f g  ) = wrap { (A <⊢ _)        }  (flip  m⊗ g)  f
      view ((A ⊗> B) <⊢ ._)  (  m⊗   f g  ) = wrap { (B <⊢ _)        }  (      m⊗ f)  g
      view (._ ⊢> (A ⇒> B))  (  m⇒   f g  ) = wrap { (_ ⊢> B)        }  (      m⇒ f)  g
      view (._ ⊢> (A <⇒ B))  (  m⇒   f g  ) = wrap { (A <⊢ _)        }  (flip  m⇒ g)  f
      view (._ ⊢> (A ⇐> B))  (  m⇐   f g  ) = wrap { (B <⊢ _)        }  (      m⇐ f)  g
      view (._ ⊢> (A <⇐ B))  (  m⇐   f g  ) = wrap { (_ ⊢> A)        }  (flip  m⇐ g)  f
      view (A <⊢ ._)         (  r⊗⇒  f    ) = wrap { ((_ ⊗> A) <⊢ _) }         r⊗⇒    f
      view (._ ⊢> (A ⇒> B))  (  r⊗⇒  f    ) = wrap { (_ ⊢> B)        }         r⊗⇒    f
      view (._ ⊢> (A <⇒ B))  (  r⊗⇒  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇒    f
      view ((A ⊗> B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (B <⊢ _)        }         r⇒⊗    f
      view ((A <⊗ B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (_ ⊢> (A <⇒ _)) }         r⇒⊗    f
      view (._ ⊢> B)         (  r⇒⊗  f    ) = wrap { (_ ⊢> (_ ⇒> B)) }         r⇒⊗    f
      view (A <⊢ ._)         (  r⊗⇐  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A ⇐> B))  (  r⊗⇐  f    ) = wrap { ((_ ⊗> B) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A <⇐ B))  (  r⊗⇐  f    ) = wrap { (_ ⊢> A)        }         r⊗⇐    f
      view ((A ⊗> B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (_ ⊢> (_ ⇐> B)) }         r⇐⊗    f
      view ((A <⊗ B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (A <⊢ _)        }         r⇐⊗    f
      view (._ ⊢> B)         (  r⇐⊗  f    ) = wrap { (_ ⊢> (B <⇐ _)) }         r⇐⊗    f

      wrap : ∀ { I : Contextʲ + } { J : Contextʲ + } {B C}
           →  (g : ∀ {G} → RM I [ G ]ʲ → RM J [ G ]ʲ) (f : RM I [ B ⇒ C ]ʲ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
```
``` hidden
  module ⇐ where

    data Origin {B C} ( J : Contextʲ + ) (f : RM J [ B ⇐ C ]ʲ) : Set where
         origin  : ∀ {E F}
                 →  (h₁  : RM B ⊢ E)
                 →  (h₂  : RM F ⊢ C)
                 →  (f′  : ∀ {G} → RM G ⊢ E ⇐ F → RM J [ G ]ʲ)
                 →  (pr  : f ≡ f′ (m⇐ h₁ h₂))
                 →  Origin J f

    mutual
      view : ∀ {B C} ( J : Contextʲ + ) (f : RM J [ B ⇐ C ]ʲ) → Origin J f
      view ([] <⊢ ._)        (  m⇐   f g  ) = origin f g id refl
      view ((A <⊗ B) <⊢ ._)  (  m⊗   f g  ) = wrap { (A <⊢ _)        }  (flip  m⊗ g)  f
      view ((A ⊗> B) <⊢ ._)  (  m⊗   f g  ) = wrap { (B <⊢ _)        }  (      m⊗ f)  g
      view (._ ⊢> (A ⇒> B))  (  m⇒   f g  ) = wrap { (_ ⊢> B)        }  (      m⇒ f)  g
      view (._ ⊢> (A <⇒ B))  (  m⇒   f g  ) = wrap { (A <⊢ _)        }  (flip  m⇒ g)  f
      view (._ ⊢> (A ⇐> B))  (  m⇐   f g  ) = wrap { (B <⊢ _)        }  (      m⇐ f)  g
      view (._ ⊢> (A <⇐ B))  (  m⇐   f g  ) = wrap { (_ ⊢> A)        }  (flip  m⇐ g)  f
      view (A <⊢ ._)         (  r⊗⇒  f    ) = wrap { ((_ ⊗> A) <⊢ _) }         r⊗⇒    f
      view (._ ⊢> (A ⇒> B))  (  r⊗⇒  f    ) = wrap { (_ ⊢> B)        }         r⊗⇒    f
      view (._ ⊢> (A <⇒ B))  (  r⊗⇒  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇒    f
      view ((A ⊗> B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (B <⊢ _)        }         r⇒⊗    f
      view ((A <⊗ B) <⊢ ._)  (  r⇒⊗  f    ) = wrap { (_ ⊢> (A <⇒ _)) }         r⇒⊗    f
      view (._ ⊢> B)         (  r⇒⊗  f    ) = wrap { (_ ⊢> (_ ⇒> B)) }         r⇒⊗    f
      view (A <⊢ ._)         (  r⊗⇐  f    ) = wrap { ((A <⊗ _) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A ⇐> B))  (  r⊗⇐  f    ) = wrap { ((_ ⊗> B) <⊢ _) }         r⊗⇐    f
      view (._ ⊢> (A <⇐ B))  (  r⊗⇐  f    ) = wrap { (_ ⊢> A)        }         r⊗⇐    f
      view ((A ⊗> B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (_ ⊢> (_ ⇐> B)) }         r⇐⊗    f
      view ((A <⊗ B) <⊢ ._)  (  r⇐⊗  f    ) = wrap { (A <⊢ _)        }         r⇐⊗    f
      view (._ ⊢> B)         (  r⇐⊗  f    ) = wrap { (_ ⊢> (B <⇐ _)) }         r⇐⊗    f

      wrap : ∀ { I : Contextʲ + } { J : Contextʲ + } {B C}
           →  (g : ∀ {G} → RM I [ G ]ʲ → RM J [ G ]ʲ) (f : RM I [ B ⇐ C ]ʲ) → Origin J (g f)
      wrap {I} {J} g f with view I f
      ... | origin h₁ h₂ f′ pr = origin h₁ h₂ (g ∘ f′) (cong g pr)
```

```
  cut′ : ∀ {A B C} → RM A ⊢ B → RM B ⊢ C → RM A ⊢ C
  cut′ {B = el     B }   f  g   with el.view ([] <⊢ _) g
  ... | el.origin           g′  _ = g′ f
  cut′ {B = B₁  ⊗  B₂}   f  g   with ⊗.view (_ ⊢> []) f
  ... | ⊗.origin h₁ h₂   f′     _ = f′ (r⇐⊗ (cut′ h₁ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ g))))))
  cut′ {B = B₁  ⇐  B₂}   f  g   with ⇐.view ([] <⊢ _) g
  ... | ⇐.origin h₁ h₂      g′  _ = g′ (r⊗⇐ (r⇒⊗ (cut′ h₂ (r⊗⇒ (cut′ (r⇐⊗ f) h₁)))))
  cut′ {B = B₁  ⇒  B₂}   f  g   with ⇒.view ([] <⊢ _) g
  ... | ⇒.origin h₁ h₂      g′  _ = g′ (r⊗⇒ (r⇐⊗ (cut′ h₁ (r⊗⇐ (cut′ (r⇒⊗ f) h₂)))))
```



### Equivalence between R and RM
``` hidden
module res⇔resmon (Atom : Set) where

  open sequent_calculus     Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open sequent_calculus⇔res Atom using (m⊗′; m⇐′; m⇒′)
  module RM = resmon Atom ; open RM
  module R = res    Atom ; open R
```


```
  from : ∀ {A B} → A R.⊢R B → A RM.⊢RM B
  from    ax           = ax′
  from (  cut  f g  )  = cut′  (from f) (from g)
  from (  r⇒⊗  f    )  = r⇒⊗   (from f)
  from (  r⊗⇒  f    )  = r⊗⇒   (from f)
  from (  r⇐⊗  f    )  = r⇐⊗   (from f)
  from (  r⊗⇐  f    )  = r⊗⇐   (from f)
```

```
  to : ∀ {A B} → A RM.⊢RM B → A R.⊢R B
  to    ax           = ax
  to (  m⊗   f g  )  = m⊗′  (to f) (to g)
  to (  m⇒   f g  )  = m⇒′  (to f) (to g)
  to (  m⇐   f g  )  = m⇐′  (to f) (to g)
  to (  r⇒⊗  f    )  = r⇒⊗  (to f)
  to (  r⊗⇒  f    )  = r⊗⇒  (to f)
  to (  r⇐⊗  f    )  = r⇐⊗  (to f)
  to (  r⊗⇐  f    )  = r⊗⇐  (to f)
```


## Derivational Semantics

``` hidden
module resmon→agda (Atom : Set) (⟦_⟧ᴬ : Atom → Set) where

  open import Function     using (id; flip; _∘_)
  open import Data.Product using (_×_; _,_; map; curry; uncurry)
  open sequent_calculus Atom using (Type; el; _⇐_; _⊗_; _⇒_)
  open resmon Atom using (_⊢RM_; ax; m⊗; m⇒; m⇐; r⇒⊗; r⇐⊗; r⊗⇒; r⊗⇐)
```

```
  ⟦_⟧ᵗ : Type → Set
  ⟦ el    A ⟧ᵗ = ⟦ A ⟧ᴬ
  ⟦ A  ⊗  B ⟧ᵗ = ⟦ A ⟧ᵗ  ×  ⟦ B ⟧ᵗ
  ⟦ A  ⇒  B ⟧ᵗ = ⟦ A ⟧ᵗ  →  ⟦ B ⟧ᵗ
  ⟦ B  ⇐  A ⟧ᵗ = ⟦ A ⟧ᵗ  →  ⟦ B ⟧ᵗ
```

```
  ⟦_⟧ : ∀ {A B} → A ⊢RM B → ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ
  ⟦ ax        ⟧ = λ x → x
  ⟦ m⊗   f g  ⟧ = λ{(x , y) → (⟦ f ⟧ x , ⟦ g ⟧ y)}
  ⟦ m⇒   f g  ⟧ = λ h x → ⟦ g ⟧ (h (⟦ f ⟧ x))
  ⟦ m⇐   f g  ⟧ = λ h x → ⟦ f ⟧ (h (⟦ g ⟧ x))
  ⟦ r⇒⊗  f    ⟧ = λ{(x , y) → ⟦ f ⟧ y x}
  ⟦ r⇐⊗  f    ⟧ = λ{(x , y) → ⟦ f ⟧ x y}
  ⟦ r⊗⇒  f    ⟧ = λ x y → ⟦ f ⟧ (y , x)
  ⟦ r⊗⇐  f    ⟧ = λ x y → ⟦ f ⟧ (x , y)

```

[^short]:  This is a slightly problematic statement: while the proofs
           *do* become shorter, in terms of the number of rules, every
           rule must be annotated with the context under which it applies.


[^prime]:  I have made it convention to label all derived and admissible rules
           with a prime. This makes it clear (without syntax highlighting) which
           rules are atomic in a system.
