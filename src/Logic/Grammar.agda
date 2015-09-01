--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Level                                 using (zero)
open import Function                              using (_∘_; flip)
open import Category.Functor                      using (module RawFunctor; RawFunctor)
open import Category.Applicative                  using (module RawApplicative; RawApplicative)
open import Category.Monad                        using (module RawMonad; RawMonadPlus)
open import Data.Bool                             using (Bool; true; false; not; T; _∧_)
open import Data.Empty                            using (⊥)
open import Data.List                             using (List; _∷_; []; _++_; map; null; any; all)
open import Data.List.NonEmpty                    using (List⁺; _∷_; foldr; foldr₁; head) renaming (map to map⁺)
open import Data.Maybe                            using (Maybe; just; nothing; monadPlus)
open import Data.Product                          using (∃; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Unit                             using (⊤; tt)
open import Reflection                            hiding (Type)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


open import Data.Traversable                      using (module RawTraversable; RawTraversable)
open import Logic.Translation                     using (module Translation)


module Logic.Grammar where



private
  instance
    rawApplicative = RawMonad.rawIApplicative (Data.List.NonEmpty.monad {f = zero})



record Grammar : Set₁ where

  infix 2 _⊢_

  -- a type theory (with a type `s' for sentences)
  field
    Type            : Set
    Struct          : Set → Set
    rawTraversable  : RawTraversable Struct
    _⊢_             : Struct Type → Type → Set
    findAll         : (Γ : Struct Type) (B : Type) → List (Γ ⊢ B)
    s               : Type

  open RawTraversable rawTraversable using (_<$>_)

  -- a translation to Agda terms
  field
    ⟦_⟧ᵗ            : Type → Set
    ⟦_⟧             : ∀ (Γ : Struct (Σ Type ⟦_⟧ᵗ)) {t} → proj₁ <$> Γ ⊢ t → ⟦ t ⟧ᵗ



record Lexicon : Set₁ where

  infix 2 Parse_as_
  infix 2 parse_as_
  infix 2 interpret_as_

  field
    grammar : Grammar

  open Grammar grammar
  open RawTraversable rawTraversable using (_<$>_; traverse)

  -- a set of words and translations to ambiguous Agda terms.
  field
    Word : Set
    Lex  : Word → List⁺ (Σ Type ⟦_⟧ᵗ)

  private
    _⊢′_ : (Γ : Struct (Σ Type ⟦_⟧ᵗ)) (t : Type) → Set
    Γ ⊢′ t = proj₁ <$> Γ ⊢ t


  -- compute an n-ary disjoint union of all possible sequent types for
  -- a given sentence.
  Parse_as_ : Struct Word → Type → Set
  Parse_as_ ws t = foldr₁ _⊎_ (map⁺ (_⊢′ t) (traverse Lex ws))


  -- attempt to parse a given sentence, returning an instance of the
  -- n-ary disjoint union above.
  parse_as_ : (ws : Struct Word) (t : Type) → List (Parse ws as t)
  parse ws as t with traverse Lex ws
  parse ws as t | Γ ∷ Γs = parse′ Γ Γs
    where
    parse′ : (Γ : _) (Γs : List _) → List (foldr₁ _⊎_ (map⁺ (_⊢′ t) (Γ ∷ Γs)))
    parse′ Γ       []  = findAll (proj₁ <$> Γ) t
    parse′ Γ (Γ′ ∷ Γs) = map inj₁ (findAll (proj₁ <$> Γ) t) ++ map inj₂ (parse′ Γ′ Γs)


  -- attempt to parse a given sentence, then translate it using the
  -- semantics function (⟦_⟧). note that since the translation inserts
  -- the interpretations of the lexical entries, this gets rid of the
  -- ambiguity in the type, and therefore the interpretation is not
  -- nested in an n-ary disjoint union.
  interpret_as_ : (ws : Struct Word) (t : Type) → List ⟦ t ⟧ᵗ
  interpret ws as t with traverse Lex ws
  interpret ws as t | Γ ∷ Γs = interpretAll Γ Γs
    where
    interpret : (Γ : Struct _) → List _
    interpret = λ Γ → map ⟦ Γ ⟧ (findAll (proj₁ <$> Γ) t)
    interpretAll : (Γ : _) (Γs : List _) → List _
    interpretAll Γ       []  = interpret Γ
    interpretAll Γ (Γ′ ∷ Γs) = interpret Γ ++ interpretAll Γ′ Γs


  -- translate a given parse using the semantics function (⟦_⟧).
  interpretParse : ∀ {ws} {t} → Parse ws as t → ⟦ t ⟧ᵗ
  interpretParse {ws} {t} with traverse Lex ws
  ... | Γ ∷ Γs = find Γ Γs
    where
      find : ∀ {t} (Γ : _) (Γs : List _)
            → foldr₁ _⊎_ (map⁺ (_⊢′ t) (Γ ∷ Γs)) → ⟦ t ⟧ᵗ
      find Γ       []        p  = ⟦ Γ ⟧ p
      find Γ (Γ′ ∷ Γs) (inj₁ p) = ⟦ Γ ⟧ p
      find Γ (Γ′ ∷ Γs) (inj₂ p) = find Γ′ Γs p


  -- a version of `Parse_as_` specialised to the sentence type.
  Parse : Struct Word → Set
  Parse ws = Parse ws as s

  -- a version of `parse_as_` specialised to the sentence type.
  parse : (ws : Struct Word) → List (Parse ws)
  parse ws = parse ws as s

  -- a version of `interpret_as_` specialised to the sentence type.
  interpret : (ws : Struct Word) → List ⟦ s ⟧ᵗ
  interpret ws = interpret ws as s


  infixr 1 ✓_ *_

  -- compute a type for which an instance can be trivially found if
  -- the given sentence parses successfully, and can never be  found
  -- if the given sentence did not. this function is meant to be used
  -- as a guard to see if a sentence parses successfully.
  ✓_ : Struct Word → Set
  ✓ ws = T (not (null (parse ws)))

  -- this function does the opposite of what `✓` above does.`
  *_ : Struct Word → Set
  * ws = T (null (parse ws))


open Grammar {{...}} using (Type; ⟦_⟧ᵗ)


fromLex : {Word : Set} (g : Grammar) (l : Word → List⁺ (Σ Type ⟦_⟧ᵗ)) → Lexicon
fromLex {Word} g l = record { grammar = g ; Word = Word ; Lex = l }


-- -}
-- -}
-- -}
-- -}
-- -}
