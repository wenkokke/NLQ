# Type-Logical Grammar
``` hidden
module type_logical_grammar where
```

The word 'type-logical grammar' goes back to @morrill1994, where it is
defined as "a refinement [of logical grammar] in which 'logical'
applies not just to logical semantics, but also to logical types
directing derivation." Thus, type-logical grammars are grammars in
which a logical system is used to describe both syntax and semantics.
The idea of having logical semantics, and a systematic translation
between syntax and semantics go back to @montague1973, whereas the
idea of logical syntax goes back to two papers written by Lambek
[-@lambek1958; -@lambek1961].

In general, type-logical grammars tend to be are substructural logics,
often fragments of non-commutative linear logic, which are designed
specifically for reasoning about the structure of natural language.
In these logical, the atomic types correspond to syntactic categories,
such as *noun*, *noun phrase* or *sentence*.
Judgements of type-correctness, then, correspond to grammaticality.
For instance, the judgement
$$\text{NP} , \; \text{NP} \to \text{S} \vdash \text{S}$$
could be taken to mean that from a noun phrase and an intransitive
verb, in that order, we can construct a valid sentence. This
corresponds to the Chomskyan grammar rule
$$\text{S} \leftarrow \text{NP} \; \text{VP}$$
However, when looking from the underlying type theory, there is one
important distinction: the type-logical statement decomposes verb
phrases into a complex type---a function from a noun phrase to a
sentence.

Below, we will briefly discuss substructural logics, and the
differences between substructural logics and more common logics such
as intuitionistic logic. We will motivate all these differences from
the perspective of our program of type-logical grammars, and give an
intuition for their use in other formalisms, such as programming
language theory. We will then spend the remainder of this section
giving an abstract definition of what type-logical grammars are, and
how they can be used.



## Substructural logic

A substructural logic is a logic which lacks one or more of the
traditional structural rules (i.e. contraction, weakening and
exchange). Below we will discuss the various effects these structural
rules have on type systems, and how they affect our program of
type-logical grammar.


### Linear logic, weakening and contraction

Discarding contraction and weakening makes logics *resource
sensitive* [@girard1987; @girard1995]. In other words, as opposed to
using *sets* of formulas as contexts, we move to using multisets or
*bags* or formulas.
Since we are planning to use the contexts to represent the sentence
structures, the move away from sets seems rather obvious.
If we were to allow weakening, we could add arbitrary words to a
sentence, without changing the grammaticality or meaning of the
sentence. For instance, "Mary read a book" would mean the same thing
as \*"Mary twelve read blue a fly bicycle book".
Contraction is a bit more subtle than weakening. If we were to allow
contraction, we could contract two words with the same syntactic
category (e.g. two adjectives) without affecting the meaning of the
sentence. This means that, for example, "a large blue book" would mean
the same thing as "a blue book" or "a large book".

In the context of type theory, recently, there has been a lot of
interest in linear type theory, where the linear properties of the
type system are exploited to allow explicit de-allocation, in-place
re-use of memory, more efficient garbage collection and safe concurrency
[see @abramsky1993; @turner1999; @igarashi2000; @plasmeijer2002; @bernardy2015].


### Ordered logic and exchange

Discarding exchange makes logics *order sensitive*, hence ordered
logic. In terms of the proof context, this means moving away from
*sets* and *bags* to lists and trees.

Because an order sensitive implication can only consume the element on
the right-most side of the antecedent, it becomes natural to add in
variants of the implication. For instance, the Lambek calculus
(section \ref{non-associative-lambek-calculus}) adds a second
implication which consumes the elements on the left-most side of the
antecedent. Displacement calculus adds in additional variants of the
implication which can consume elements wrapped around or nested in the
antecedent [see @morrill2011].

The structural rule of exchange can be decomposed into two separate
rules with respect to the structure-forming connectives---usually a
comma. These rules are commutativity and  associativity.
If we were to allow commutativity, we could arbitrarily change the
order of the words, without affecting the grammaticality of the
sentence. For instance, "Mary read a book" would mean the same thing
as \*"book Mary a read".

The original system for type-logical grammars formulated in @lambek1958
included associativity. This seemed to be a sound choice, as it
allowed the system to check the grammaticality of strings of words, or
lists of formulas, as opposed to trees. However, in allowing
associativity, one invariably allows some undesirable sentences to be
accepted as grammatical [see @moot2012, pp. 105-106].
One example of this is is that in the calculus *with* associativity,
|(n ⇐ n) ⊗ (n ⇐ n) ⊢ n ⇐ n| (i.e. left function composition) is a
theorem. Since the most natural type assignment for adjectives and the
verb "to be" are |n ⇐ n| and |(np ⇒ s) ⇐ (n ⇐ n)| respectively, the
sentence \*"The Hulk is green incredible" becomes derivable.

In the context of type theory, Some work has been done in the field of
ordered type theory, where the order sensitivity of the calculus is
used to achieve even more efficient memory management, which is
possible due to having an even more fine-grained type system than
linear logic: theoretically, any program typed in an ordered type
theory can be run using only a stack as memory [see @petersen2003].


### Unit elements and empty sequences

Though the removal of unit elements is uncommon in type theory, it is
nonetheless essential for our program [see @moot2012, pp. 33].
The reason for this is that if we were to allow unit elements (or
empty antecedents) |𝟙 ⊢ n ⇐ n| would be a theorem. Joined with the
fact that |(n ⇐ n) ⇐ (n ⇐ n)| is a natural type for "very", we can see
that we could supply the empty sequence as the first argument for
"very". We could use this trick to show that, for instance, \*"a very
book" is grammatical.



## Structures and grammaticality
``` hidden
module structures_and_grammaticality where

  open import Level using (zero)
  open import Category.Functor using (module RawFunctor; RawFunctor)
  open import Category.Monad using (module RawMonad; RawMonadPlus)
  open import Data.Bool using (T; not)
  open import Data.List as List using (List; _∷_; []; _++_; map; null)
  open import Data.List.NonEmpty as NonEmpty using (List⁺; _∷_; foldr₁) renaming (map to map⁺)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Data.Traversable using (module RawTraversable; RawTraversable)
  open RawFunctor {{...}} using (_<$>_)
```
A type-logical grammar consists of a decidable type theory with a type
|s| for sentences, and a set of words with possibly ambiguous type
assignments:
```
  record TypeLogicalGrammar : Set₁ where

    field
      Type            : Set
      Struct          : Set → Set
      rawTraversable  : RawTraversable Struct
      _⊢_             : Struct Type → Type → Set
      s               : Type
      findAll         : (Γ : Struct Type) (B : Type) → List (Γ ⊢ B)

      Word            : Set
      Lex             : Word → List⁺ Type
```
``` hidden
    infixr 1 ✓_ *_
    infixr 2 _⊢_

    open RawTraversable rawTraversable using (traverse)
    instance listApplicative = RawMonad.rawIApplicative (NonEmpty.monad {f = zero})
```
Typically, the set of syntactic categories -- or *types* -- is built
up over a set of atomic types (usually |n|, |np| and |s|), a product
(|⊗|) and two directional implications
[written |⇒| and |⇐|, after @ajdukiewicz1935].

The |Struct| represents the structure of the antecedent, which is
usually instantiated to a list (if classify strings) or a binary
tree (if we classify constituency trees). However, it is safe to think
of this structure as always being a binary tree, as other common
structures (list, bag, set) are degenerate cases of binary trees under
certain axioms (associativity, commutativity, contraction).

In addition, the |Struct| is required to be traversable, which means
that it is required to implement the |traverse| function (where F is
an applicative functor):
\begin{spec}
traverse : (A → F B) → Struct A → F (Struct B)
\end{spec}
For a quick intuition, |traverse| is like |map| (or `⟨$⟩`) in that it
allows you to apply a function to every element of a
structure. However, it also allows you to have effects like |IO| and
ambiguity (i.e. |List|) while rebuilding the data structure
[see @mcbride2008].

Furthermore, the typing relation `⊢` is required to be at least a
preorder, and often forms a residuated algebra or lattice.
However, the asymmetry of its type prevents us from expressing this
directly.

Note that because the structure of a type-logical grammar as defined
above is not explicitly paired with a structure over `⊢`, it is not
possible to *derive* any theorems in it.
Therefore, in order to make this a useful structure, we have included
the requirement that the the typing relation must be
decidable through the decision procedure |findAll|.

Because it isn't possible to form any other sequents than `_⊢ s` using
the definition above, it may be prudent to replace |s| and `⊢` with a
single predicate |Valid|. However, we feel that this would obscure the
type-logical nature of the grammars too much, and therefore have opted
to keep them separate.

Using an instance of a type-logical grammar, we can compute the
statement that a given sentence (represented as a structure of words)
is grammatical:
```
    Parse : Struct Word → Set
    Parse ws = foldr₁ _⊎_ (map⁺ (_⊢ s) (traverse Lex ws))
```
The above function:

 1. traverses the given sentence structure, and looks up the possible
    ambiguous interpretations for each word, resulting in a list of
    all possible interpretations for the given sentence; then
 2. for each interpretation |Γ|, forms the judgement |Γ ⊢ s|; and lastly,
 3. joins the list of possible judgements with the disjoint union (|⊎|).

This results in a type for which an inhabitant can be given by 1)
selecting the correct interpretation of the sentence using |inj₁| and
|inj₂|, and 2) giving a derivation for the chosen interpretation.

In addition, because we have required the typing relation to be
decidable, we can implement a function called |parse|, which uses the
decision procedure to try and parse a given sentence:
```
    parse : (ws : Struct Word) → List (Parse ws)
    parse ws with traverse Lex ws
    parse ws | Γ ∷ Γs = parse′ Γ Γs
      where
        parse′ : (Γ : _) (Γs : List _) → List (foldr₁ _⊎_ (map⁺ (_⊢ s) (Γ ∷ Γs)))
        parse′ Γ       []  = findAll Γ s
        parse′ Γ (Γ′ ∷ Γs) = map inj₁ (findAll Γ s) ++ map inj₂ (parse′ Γ′ Γs)
```
The function |parse| will generate the same sequence of potential
interpretations as |✓|, and then try to prove them all in
succession, wrapping them it in the correct prefix of |inj₁|s and
|inj₂|s.  Should none of the interpretations be valid, it will return
the empty list.

We can now use a trick from dependently-typed programming. Below we
define a function |✓|, which evaluations the expression |parse ws| at
compile time, for a known |ws|, and checks that it is successful. The
function |T| is defined as follows:
\begin{spec}
T : Bool → Set
T true   =  ⊤
T false  =  ⊥
\end{spec}
Thus, in the case that |parse| succeeds, the type below evaluates to
the unit type |⊤|, which has only one inhabitant (|tt|) and can
therefore be inferred. However, should |parse| fail, the type
evaluates to the empty type |⊥|, for which no inhabitant exists.

Using this trick we can define |✓| in such a way that it checks
whether or not |parse ws| succeeds during type checking, and results
in a type error if it does not:

```
    ✓_ : Struct Word → Set
    ✓ ws = T (not (null (parse ws)))
```
Analogously, we can define the function |*|, which attempts to parse
the sentence, and ensures that the parse is not successful. This will
allow you to write out claims about sentences which should not and are
not accepted by your grammar:
```
    *_ : Struct Word → Set
    * ws = T (null (parse ws))
```
``` hidden
module example₁ where
  open import Example.System.AlgLG
```
Given a type-logical grammar with the necessary words in its lexicon, we
may now formulate statements of grammaticality. For instance:
``` hidden
  example₁ :
```
```
    ✓ · mary · , · finds · , · a · , · unicorn ·
```
``` hidden
  example₁ = _
  example₂ :
```
```
    ✓ (· a · , · unicorn ·) , · finds · , · mary ·
```
``` hidden
  example₂ = _
  example₃ :
```
```
    * · unicorn · , · mary · , · a · , · finds ·
```
``` hidden
  example₃ = _
```
The fact that the above code compiles is witness to the fact that
"mary finds a unicorn" and "a unicorn finds mary" are accepted by our
grammar, but \*"unicorn mary a finds" is not.



## Unit testing semantics
``` hidden
module unit_testing_semantics where

  open import Level                   using (zero)
  open import Category.Functor        using (module RawFunctor; RawFunctor)
  open import Category.Monad          using (module RawMonad; RawMonadPlus)
  open import Data.Bool               using (Bool; T; not)
  open import Data.List          as L using (List; _∷_; []; _++_; map; null)
  open import Data.List.NonEmpty as N using (List⁺; _∷_; foldr₁) renaming (map to map⁺)
  open import Data.Product            using (Σ; Σ-syntax; proj₁)
  open import Data.Sum                using (_⊎_; inj₁; inj₂)
  open import Data.Traversable        using (module RawTraversable; RawTraversable)
  open import Function                using (_∘_)
  open RawFunctor {{...}} renaming (_<$>_ to _⟨$⟩_)
```
In the previous section we gave a definition of type-logical grammars
which allowed us define two operators `✓` and `*`, which can asses the
grammaticality and ungrammaticality, respectively, of sentences at
compile time. In this section, we will expand on this definition by
adding a pair of operators `⟦_⟧` and |↦|, which will compute a list of
all possible interpretations of a given sentence, and compare two
lists of terms, respectively.

While type-logical grammars can express their semantics in any sort of
theory, we are going limit our definition to expressing its semantics
in Agda. This is extremely practical, because it allows us to evaluate
and inspect semantic expressions, implement models, add and remove
meaning postulates on the fly, compare terms, and do all this with
almost no implementation effort.
``` hidden
  record TypeLogicalGrammar : Set₁ where
    infix 2 _⊢_
    field
      Type            : Set
      Struct          : Set → Set
      rawTraversable  : RawTraversable Struct
      _⊢_             : Struct Type → Type → Set
      findAll         : (Γ : Struct Type) (B : Type) → List (Γ ⊢ B)
      s               : Type
      Word            : Set
      toAgdaType      : Type → Set

    open RawTraversable rawTraversable using (traverse)
    instance listApplicative = RawMonad.rawIApplicative (N.monad {f = zero})
    private
      instance
        rawFunctor = RawTraversable.rawFunctor rawTraversable
```
We would like to extend the previous definition for type-logical
grammars with the two following functions:
\begin{spec}
    field
      toAgdaType : Type → Set
      toAgdaTerm : Γ ⊢ B → toAgdaType B
\end{spec}
One function to convert types in our grammar to types in Agda -- denoted
by "the type of types" |Set|. Our second function would ideally take
proofs in our grammar, and return well-typed Agda programs. However,
as it stands, there are some problems with the above type. First, the
term |Γ ⊢ B| is not closed, and therefore cannot be translated to an
Agda program of type |toAgdaType B|. Moreover, the decision to ban
empty contexts and unit types means that the term cannot possibly be
closed.
This means that we somehow have to translate our term |Γ ⊢ B| to a
function.

One option would be to translate it as a function, but then we would
need some translation |f| from contexts |Struct Type| to |Set|, and a
translation of values of type |Γ : Struct Type| to values of type |f
Γ|. We would rather not do this, as not only would we have to add two
new functions to the definition of type-logical grammars, but we would
also have to find a way to insert the denotations associated with the
types into the the term, something that is not entirely trivial when
are trying to stay agnostic to the specific implementation of |Struct|!

A more reasonable alternative is to redefine our lexicon function to
provide not only the type of words, but also their denotation, wrapped
in a sigma type:
```
    field
      Lex : Word → List⁺ (Σ[ A ∈ Type ] (toAgdaType A))
```
This means that our lexicon function will return a list of pairs for
each word, where the first element of the pair is its syntactic
category, and the second element is its denotation, typed by the
translation of its syntactic category to an Agda type.
``` hidden
    private
      module Old = structures_and_grammaticality
      typeLogicalGrammar : Old.TypeLogicalGrammar
      typeLogicalGrammar = record
          { Type           = Type
          ; Struct         = Struct
          ; rawTraversable = rawTraversable
          ; Word           = Word
          ; Lex            = map⁺ proj₁ ∘ Lex
          ; s              = s
          ; _⊢_            = _⊢_
          ; findAll        = findAll
          }
      open Old.TypeLogicalGrammar typeLogicalGrammar public using (✓_; *_)
```
Now we can define the type for |toAgdaTerm|: it will be a function
which takes a structure |Γ|, populated by both types and terms, and a
term which has as its context only the types in |Γ|:
```
    field
      toAgdaTerm  :  (Γ : Struct (Σ[ A ∈ Type ] (toAgdaType A)))
                  →  (proj₁ ⟨$⟩ Γ) ⊢ s
                  →  toAgdaType s
```
And using these functions, we can define the function `⟦_⟧`:
```
    ⟦_⟧ : (ws : Struct Word) → List (toAgdaType s)
    ⟦ ws ⟧  with traverse Lex ws
    ⟦ ws ⟧  | Γ ∷ Γs = ⟦⟧-all Γ Γs
      where
        ⟦⟧-one  : (Γ : Struct _) → List _
        ⟦⟧-one  Γ = map (toAgdaTerm Γ) (findAll (proj₁ ⟨$⟩ Γ) s)

        ⟦⟧-all  : (Γ : _) (Γs : List _) → List _
        ⟦⟧-all  Γ        []   = ⟦⟧-one Γ
        ⟦⟧-all  Γ (Γ′ ∷  Γs)  = ⟦⟧-one Γ ++ ⟦⟧-all Γ′ Γs
```
The helper function `⟦⟧-one` takes a single interpretation of
sentence, finds all the proofs of that interpretation, and then
transforms those proofs into Agda terms. The helper function `⟦⟧-all`
then applies this function to all possible interpretations of a
sentence.
``` hidden
module example₂ where
  open import Data.List using (_∷_; [])
  open import Example.System.AlgNL
  open import assertions public using (_↦_)
```
We assume a simple set of meaning postulates, and a suitable
type-logical grammar (we use the non-associative Lambek calculus for
these examples, see section \ref{non-associative-lambek-calculus}):
\begin{spec}
  postulate
    FORALL     : (Entity → Bool) → Bool
    EXISTS     : (Entity → Bool) → Bool
    MARY       : Entity
    FINDS      : Entity → Entity → Bool
    UNICORN    : Entity → Bool
    PERSON     : Entity → Bool
    LOVES      : Entity → Entity → Bool
\end{spec}
Using our newly defined interpretation function `⟦_⟧`, and the
function `↦`, we can now make claims about the interpretation of
sentences, for instance:
``` hidden
  example₄  :
```
```
    ⟦ · mary · , · finds · , · a · , · unicorn · ⟧
      ↦ EXISTS (λ y → UNICORN y ∧ MARY FINDS y)
```
``` hidden
  example₄  = _
```
However, if the sentence is ambiguous, we can provide a list as the
second argument, which is where `↦` really starts becoming useful:
``` hidden
  example₅  :
```
```
    ⟦ · someone · , · loves · , · everyone · ⟧
      ↦  EXISTS  (λ x  → PERSON x  ∧  FORALL  (λ y  →  PERSON y  ⊃  x LOVES y))
      ∷  FORALL  (λ y  → PERSON y  ⊃  EXISTS  (λ x  →  PERSON x  ∧  x LOVES y))
      ∷  []
```
``` hidden
  example₅ = _
```
Note that we have not yet discussed the implementation of the `↦`
function. We feel it would be best to postpone a detailed discussion
of its implementation, as the features of Agda it uses are rather
intricate. In short, it is a macro which obtains the abstract syntax
for the terms on its either side and compares them for equality. The
reason this works is because the abstract syntax is *normalised* and
uses *de Bruijn indices*.

TODO: make sure such a discussion of `↦` happens.

Ideally, we would like to define another function, `#`, which would
formalise the way '#' is used in linguistics papers. We can approach
the semantics of '#' using the functions `[_]` and `↦` defined above,
but this does not quite capture the precise meaning of '#'---the
operator does not describe "has the right semantics" as much as "is
semantically well-typed". This is the reason why it is appropriate to
say that \#"green ideas sleep furiously", even though it is a
grammatical sentence.
The way I would envision implementing it would be as follows: we would
take the usual apparatus of categorial grammar (a syntactic calculus
and a translation into the simply typed lambda calculus with *e* and
*t* or `Entity` and `Bool` as its primitive types. Then, after the
derivation of a proof that the sentence is grammatical, and is
translated into this *et*-typed calculus, we attempt to translate it
into a more strictly typed semantic calculus. If this succeeds, then
we say it is semantically sound. If it does not, then apparently the
sentence is semantically unsound. However, implementing a more
strictly typed semantic calculus is beyond the scope of this thesis.
