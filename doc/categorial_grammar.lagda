``` hidden
open import Level                                 using (suc; _⊔_)
open import Data.List                             using (List ; _∷_; []; zipWith)
open import Data.List.NonEmpty                    using (List⁺; _∷_; foldr₁) renaming (map to mapᴸ)
open import Data.Sum                              using (_⊎_)
open import Function                              using (_∘_; _$_)
open import Relation.Binary                       using (IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_)

module categorial_grammar where

infixr 4 _,_
```

# Categorial Grammar

Overview.

Discuss what categorial grammar is.

``` hidden

```

```
data Struct {a} (A : Set a) : Set a where
  ·_·  : A                    → Struct A
  _,_  : Struct A → Struct A  → Struct A
```

``` hidden
mapᵀ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Struct A → Struct B
mapᵀ f ·  x  · = · f x ·
mapᵀ f (l , r) = (mapᵀ f l , mapᵀ f r)
```

A categorial grammar contains the following fields:
```
record CategorialGrammar : Set₁ where
```
``` hidden
  infixr 1 ✓_
  infixr 6 _⊗_
  infixr 5 _⇒_
  infixl 5 _⇐_

  field
```
A set of syntactic categories---here referred to as
types. Traditionally, the connectives that build up syntactic
categories are a product (|⊗|) and two directional implications
[written |⇒| and |⇐|, after @ajdukiewicz1935]:
```
    Type        : Set
    _⊗_         : Type → Type → Type
    _⇐_         : Type → Type → Type
    _⇒_         : Type → Type → Type
```

A set of words, and a lexicon which assigns a finite list of types to
each word:
```
    Word        : Set
    Lex         : Word → List⁺ Type
```

And lastly, some type |Start|, which represents the type for
grammatical sentences, and a preorder |≤|, which expresses
derivability between syntactic categories:
```
    Start       : Type
    _≤_         : Type → Type → Set
    isPreorder  : IsPreorder _≡_ _≤_
```

Compute the statement that a certain sentence with a certain structure
is grammatical:
```
  ✓_ : Struct Word → Set
  ✓ t = foldr₁ _⊎_ (mapᴸ ((_≤ Start) ∘ flatten) (amb (mapᵀ Lex t)))
```
``` hidden
    where
```

Convert a single ambiguous tree to a list of unambiguous trees:
```
      amb : Struct (List⁺ Type) → List⁺ (Struct Type)
      amb  ·   x    ·  = mapᴸ ·_· x
      amb  (l  , r  )  = amb l ,⁺ amb r
```
``` hidden
        where
          _,⁺_ : List⁺ (Struct Type) → List⁺ (Struct Type) → List⁺ (Struct Type)
          (x ∷ xs) ,⁺ (y ∷ ys) = (x , y) ∷ zipWith _,_ xs ys
```

Flatten a structure down to a type:
```
      flatten : Struct Type → Type
      flatten ·  x  · = x
      flatten (l , r) = flatten l ⊗ flatten r
```

``` hidden
module _ (cg : CategorialGrammar) where

  open CategorialGrammar cg

  module _ (mary finds a unicorn : Word) where
```
Given a categorial grammar with the necessary words in its lexicon, we
may now formulate statements of grammaticality. For instance:
``` hidden
    MARY_FINDS_A_UNICORN : Set
    MARY_FINDS_A_UNICORN =
```
```
      ✓ · mary · , · finds · , · a · , · unicorn ·
```
This value evaluates to a type, and if we are able to show that this
type has an inhabitant, we have shown that the sentence "Mary finds a
unicorn" is accepted by our grammar.

\todo{Discuss the pairing of a categorial grammar with various
structures. The requirement of a preorder is the minimal requirement
in order to be able to call our approach "type-logical grammar" or the
underlying system a type system.}

\todo{Discuss replacing the preorder requirement with something like
intuitionistic logic.}

\todo{Explain why we need to drop commutativity of the product (|⊗|).}
\todo{Explain why we need to drop weakening.}
\todo{Explain why we need to drop contraction.}
\todo{Explain why we need to drop associativity.}
\todo{Explain why we need to drop the empty sequent.}
