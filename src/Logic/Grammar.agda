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
open import Data.List.NonEmpty                    using (List⁺; _∷_; foldr; foldr₁) renaming (map to map⁺)
open import Data.Maybe                            using (Maybe; just; nothing; monadPlus)
open import Data.Product                          using (Σ; Σ-syntax; _×_; proj₁; proj₂)
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
    ⟦_⟧             : (Γ : Struct (Σ Type ⟦_⟧ᵗ)) → proj₁ <$> Γ ⊢ s → ⟦ s ⟧ᵗ



record Lexicon : Set₁ where

  field
    grammar : Grammar

  open Grammar grammar
  open RawTraversable rawTraversable using (_<$>_; traverse)

  -- a set of words and translations to ambiguous Agda terms
  field
    Word : Set
    Lex  : Word → List⁺ (Σ Type ⟦_⟧ᵗ)


  Parse : Struct Word → Set
  Parse ws = foldr₁ _⊎_ (map⁺ (_⊢ s) (traverse (map⁺ proj₁ ∘ Lex) ws))


  parse : (ws : Struct Word) → List (Parse ws)
  parse ws with traverse (map⁺ proj₁ ∘ Lex) ws
  parse ws | Γ ∷ Γs = parse′ Γ Γs
    where
      parse′ : (Γ : _) (Γs : List _) → List (foldr₁ _⊎_ (map⁺ (_⊢ s) (Γ ∷ Γs)))
      parse′ Γ       []  = findAll Γ s
      parse′ Γ (Γ′ ∷ Γs) = map inj₁ (findAll Γ s) ++ map inj₂ (parse′ Γ′ Γs)


  interpret : (ws : Struct Word) → List ⟦ s ⟧ᵗ
  interpret ws with traverse Lex ws
  interpret ws | Γ ∷ Γs = forAll Γ Γs
    where
      forOne : (Γ : Struct _) → List _
      forOne = λ Γ → map ⟦ Γ ⟧ (findAll (proj₁ <$> Γ) s)
      forAll : (Γ : _) (Γs : List _) → List _
      forAll Γ       []  = forOne Γ
      forAll Γ (Γ′ ∷ Γs) = forOne Γ ++ forAll Γ′ Γs


  infixr 1 ✓_ *_

  ✓_ : Struct Word → Set
  ✓ ws = T (not (null (parse ws)))

  *_ : Struct Word → Set
  * ws = T (null (parse ws))


open Grammar {{...}} using (Type; ⟦_⟧ᵗ)


fromLex : {Word : Set} (g : Grammar) (l : Word → List⁺ (Σ Type ⟦_⟧ᵗ)) → Lexicon
fromLex {Word} g l = record { grammar = g ; Word = Word ; Lex = l }
