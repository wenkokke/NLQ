``` hidden
open import Level
open import Category.Applicative                  using (module RawApplicative; RawApplicative)
open import Category.Monad                        using (module RawMonad; RawMonadPlus)
open import Data.Bool                             using (T)
open import Data.List                             using (List; _∷_; [])
open import Data.List.NonEmpty                    using (List⁺; _∷_; [_]; map; foldr; foldr₁)
open import Data.Maybe                            hiding (Is-just; map)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Traversable                      using (module RawTraversable) renaming (RawTraversable to Traversable)
open import Data.Unit                             using (⊤; tt)
open import Function                              using (_∘_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module categorial_grammar where

infixr 4 _,_
```

# Categorial Grammar

## Structures and grammaticality

A categorial grammar consists of the following objecs:
```
record CategorialGrammar : Set₁ where
  field
    Type         : Set
    Struct       : Set → Set
    traversable  : Traversable Struct
    Word         : Set
    Lex          : Word → List⁺ Type
    s            : Type
    _⊢_          : Struct Type → Type → Set
    _⊢?_         : ∀ Γ B → Maybe (Γ ⊢ B)
```
``` hidden
  open RawTraversable traversable                     using (traverse)
  open RawMonad (Data.Maybe.monad {f = zero})         using (_<$>_)
  open RawMonad (Data.List.NonEmpty.monad {f = zero}) using (rawIApplicative)
  instance rawApplicative = rawIApplicative
```
Typically, the set of syntactic categories is built up over a set of
atomic types (usually |n|, |np| and |s|), a product (|⊗|) and two
directional implications
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
traverse : ∀ {F A B} → (A → F B) → Struct A → F (Struct B)
\end{spec}
For a quick intuition, |traverse| is like |map| in that it allows you
to apply a function to every element of a structure. However, it also
allows you to have effects like |IO| and ambiguity (i.e. |List|)
while rebuilding the data structure [see @mcbride2008].

Furthermore, the typing relation |⊢| is required to be at least a
preorder, and often forms a residuated algebra or lattice.
However, the asymmetry of its type prevents us from expressing this
directly.

Note that because the structure of a categorial grammar as defined
above is not explicitly paired with a structure over |⊢|, it is not
possible to *derive* any theorems in it. This is atypical, as the term
"categorial grammar" is usually associated with the above structure
paired with a residuated algebra or lattice.
Therefore, in order to make this a useful structure, we have included
the requirement that the the typing relation is decidable---through the
decision procedure |⊢?|.

Because it isn't possible to form any other sequents than |_⊢ s| using
the definition above, it may be prudent to replace |s| and |⊢| with a
single predicate |Valid|. However, we feel that this would obscure the
type-logical nature of the grammars too much, and therefore have opted
to keep them separate.

Using an instance of a categorial grammar, we can compute the
statement that a given sentence (represented as a structure of words)
is grammatical:
```
  ✓ : Struct Word → Set
  ✓ ws = foldr₁ _⊎_ (map (_⊢ s) (traverse Lex ws))
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
  parse : (ws : Struct Word) → Maybe (✓ ws)
```
``` hidden
  parse ws with traverse Lex ws
  parse ws | Γ ∷ Γs = parse′ Γ Γs
    where
      parse′  : ∀ Γ Γs → Maybe (foldr₁ _⊎_ (map (_⊢ s) (Γ ∷ Γs)))
      parse′ Γ        []   = Γ ⊢? s
      parse′ Γ (Γ′ ∷  Γs)  with (Γ ⊢? s)
      parse′ Γ (Γ′ ∷  Γs)  | just pr  = just (inj₁ pr)
      parse′ Γ (Γ′ ∷  Γs)  | nothing  = inj₂ <$> parse′ Γ′ Γs
```
The function parse will generate the same list of potential
interpretations as |✓|, and then try to prove them all in
succession, stopping at the first successful parse and wrapping it in
the correct prefix of |inj₁|s and |inj₂|s and a |just|.
Should none of the interpretations be valid, it will return |nothing|.

We can now use a trick from dependently-typed programming. Below we
define a function |✓?|, which evaluations the expression |parse ws| at
compile time, for a known |ws|, and checks that it is successful. The
function |T| is defined as follows:
\begin{spec}
T : Bool → Set
T true   =  ⊤
T false  =  ⊥
\end{spec}
Thus, in the case that |parse| succeeds, the type of the implicit
argument |p| below evaluates to the unit type |⊤|, which has only one
inhabitant (|tt|) and can therefore be inferred. However, should
|parse| fail, the type of |p| evaluates to the empty type |⊥|, for
which no inhabitant exists.

Using this trick we can define |✓?| in such a way that it checks
whether or not |parse ws| succeeds during type checking, and results
in a type error if it does not:
``` keep_implicit_args
  ✓?  : ∀ ws → {p : T (is-just (parse ws))} → ✓ ws
  ✓? ws {p = _   } with parse ws
  ✓? ws {p = tt  } | just pr = pr
  ✓? ws {p = ()  } | nothing
```
Note that because we have ensured that |parse ws| succeeds, we can
safely return the successful parse.

Analogously, we can define the slightly less informative function
|*?|, which attempts to parse the sentence, and ensures that the parse
is not successful. This will allow you to write out claims about
sentences which should not and are not accepted by your grammar:
``` keep_implicit_args
  *?  : ∀ ws → {p : T (is-nothing (parse ws))} → ⊤
  *? ws {p =  _  } with parse ws
  *? ws {p = ()  } | just pr
  *? ws {p = tt  } | nothing = tt
```
The reason the above definition is less useful is related the type we
have given the decision procedure |⊢?|: if possible, it returns a
proof of the given judgement. However, if it fails, it needs to
provide |nothing|. This means that only the true-positives of our
decision procedure are verified. A fully-verified decision procedure
would also have to provide a proof of non-inhabitation in the negative
case:
\begin{spec}
  data Dec {p} (P : Set p) : Set p where
    yes : ( p  :    P) → Dec P
    no  : (¬p  : ¬  P) → Dec P
\end{spec}
However, it is generally much more difficult to prove that something
*cannot* be derived in a certain logical system, than it is to prove
that something *can* be derived. Therefore, as to not make it too
difficult to provide an instance of |CategorialGrammar|, we have opted
to allow for this slight deviation from our program of strict
formalisation.
``` hidden
data Atom : Set where
  N  : Atom
  NP : Atom
  S  : Atom

_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)
N  ≟-Atom N  = yes refl
N  ≟-Atom NP = no (λ ())
N  ≟-Atom S  = no (λ ())
NP ≟-Atom N  = no (λ ())
NP ≟-Atom NP = yes refl
NP ≟-Atom S  = no (λ ())
S  ≟-Atom N  = no (λ ())
S  ≟-Atom NP = no (λ ())
S  ≟-Atom S  = yes refl

open import Logic.Intuitionistic.Ordered.Lambek.ResMon             Atom
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.ProofSearch Atom _≟-Atom_

s n np : Type
s  = el S
n  = el N
np = el NP
```
Using these two operators, and assuming an implementation of we can now
```
data Word : Set where
  mary     : Word
  finds    : Word
  a        : Word
  unicorn  : Word
```
```
Lex : Word → List⁺ Type
Lex mary     = [ np             ]
Lex finds    = [ (np ⇒ s) ⇐ np  ]
Lex a        = [ np ⇐ n         ]
Lex unicorn  = [ n              ]
```

```
data Struct {a} (A : Set a) : Set a where
  ·_·  : A                    → Struct A
  _,_  : Struct A → Struct A  → Struct A
```

``` hidden
traversable : ∀ {a} → Traversable {a} Struct
traversable = record { traverse = traverse  }
  where
    open RawApplicative {{...}}
    traverse : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → Struct A → F (Struct B)
    traverse f  ·   x    · = ·_· <$> f x
    traverse f  (l  , r  ) = _,_ <$> traverse f l ⊛ traverse f r

lambekGrammar : CategorialGrammar
lambekGrammar = record
  { Type        = Type
  ; Struct      = Struct
  ; traversable = traversable
  ; Word        = Word
  ; Lex         = Lex
  ; s           = el S
  ; _⊢_         = λ Γ B → NL flatten Γ ⊢ B
  ; _⊢?_        = λ Γ B → maybeFind (flatten Γ ⊢ B)
  }
  where
    flatten : Struct Type → Type
    flatten ·  x  · = x
    flatten (l , r) = flatten l ⊗ flatten r

open CategorialGrammar lambekGrammar using (✓; ✓?)
```

Given a categorial grammar with the necessary words in its lexicon, we
may now formulate statements of grammaticality. For instance:
``` hidden
example₁ : ✓   (· mary · , · finds · , · a · , · unicorn ·)
example₁ =
```
```
  ✓?  (· mary · , · finds · , · a · , · unicorn ·)
```
This value evaluates to a type, and if we are able to show that this
type has an inhabitant, we will have shown that the sentence "Mary
finds a unicorn" is accepted by our grammar.

\todo{Discuss the pairing of a categorial grammar with various
structures. The requirement of a preorder is the minimal requirement
in order to be able to call our approach "type-logical grammar" or the
underlying system a type system.}

\todo{Discuss replacing the preorder requirement with something like
intuitionistic logic.}
