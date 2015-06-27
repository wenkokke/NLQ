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

## Structures and grammaticality


``` hidden
data Struct {a} (A : Set a) : Set a where
  ·_·  : A                    → Struct A
  _,_  : Struct A → Struct A  → Struct A

mapᵀ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Struct A → Struct B
mapᵀ f ·  x  · = · f x ·
mapᵀ f (l , r) = (mapᵀ f l , mapᵀ f r)
```

A categorial grammar consists of the following objecs:
```
record CategorialGrammar : Set₁ where
  field
    Type  : Set                       -- a set of syntactic categories
    Word  : Set                       -- a set of words
    lex   : Word → List⁺ Type         -- a lexicon, which assigns a finite
                                      -- non-empty list of types to each word
    s     : Type                      -- a type of well-formed sentences
    _⊢_   : Struct Type → Type → Set  -- a typing relation
```
``` hidden
  infixr 1 ✓_
```
Typically, the set of syntactic categories is built up over a set of
atomic types (usually |n|, |np| and |s|), a product (|⊗|) and two
directional implications [written |⇒| and |⇐|, after @ajdukiewicz1935].
Furthermore, the typing relation |⊢| is required to be at least a
preorder, and often forms a residuated algebra or lattice. However, the
asymmetry of its type prevents us from expressing this directly.
In addition, for the sake of parsing, the typing relation is usually
required to be decidable.

Compute the statement that a certain sentence with a certain structure
is grammatical:
```
  ✓_ : Struct Word → Set
  ✓ sent = foldr₁ _⊎_ (mapᴸ (λ ts → ts ⊢ s) (amb (mapᵀ lex sent)))
```
``` hidden
    where
```

Convert a single ambiguous tree to a list of unambiguous trees:
``` hidden
      amb : Struct (List⁺ Type) → List⁺ (Struct Type)
      amb  ·   x    ·  = mapᴸ ·_· x
      amb  (l  , r  )  = amb l ,⁺ amb r
        where
          _,⁺_ : List⁺ (Struct Type) → List⁺ (Struct Type) → List⁺ (Struct Type)
          (x ∷ xs) ,⁺ (y ∷ ys) = (x , y) ∷ zipWith _,_ xs ys
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
      ✓ (· mary · , · finds · , · a · , · unicorn ·)
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
