--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------

open import Category.Functor                            using (module RawFunctor; RawFunctor)
open import Category.Applicative                        using (module RawApplicative; RawApplicative)
open import Category.Monad                              using (module RawMonad; RawMonadPlus)
open import Data.Bool                                   using (Bool; true; false; not; T; _∧_)
open import Data.Empty                                  using (⊥)
open import Data.Foldable                               using (module RawFoldable; RawFoldable)
open import Data.List                                   using (List; _∷_; []; _++_; map; null; any; all)
open import Data.List.NonEmpty                          using (List⁺; _∷_; foldr; foldr₁) renaming (map to map⁺)
open import Data.Maybe                                  using (Maybe; just; nothing; monadPlus)
open import Data.Monoid                                 using (module RawMonoid; RawMonoid)
open import Data.Product                                using (Σ; Σ-syntax; _×_; proj₁; proj₂)
open import Data.Sum                                    using (_⊎_; inj₁; inj₂)
open import Data.Traversable                            using (module RawTraversable; RawTraversable)
open import Data.Unit                                   using (⊤; tt)
open import Function                                    using (_∘_; flip)
open import Level                                       using (zero)
open import Logic.Translation                           using (module Translation)
open import Logic.Intuitionistic.Unrestricted.Agda.Show using (show)
open import Reflection                                  hiding (Type)
open import Relation.Nullary                            using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality       using (_≡_; refl)


module TypeLogicalGrammar where


private
  instance
    rawApplicative = RawMonad.rawIApplicative (Data.List.NonEmpty.monad {f = zero})


record TypeLogicalGrammar : Set₁ where

  infix 2 _⊢_

  -- a type theory (with a type `s' for sentences)
  field
    Type            : Set
    Struct          : Set → Set
    rawTraversable  : RawTraversable Struct
    _⊢_             : Struct Type → Type → Set
    findAll         : (Γ : Struct Type) (B : Type) → List (Γ ⊢ B)
    s               : Type

  open RawTraversable rawTraversable using (_<$>_; traverse)

  -- a translation to Agda terms
  field
    toAgdaType  : Type → Set
    toAgdaTerm  : (Γ : Struct (Σ Type toAgdaType)) → proj₁ <$> Γ ⊢ s → toAgdaType s

  -- a set of words and translations to ambiguous Agda terms
  field
    Word            : Set
    Lex             : Word → List⁺ (Σ Type toAgdaType)

  Parse : Struct Word → Set
  Parse ws = foldr₁ _⊎_ (map⁺ (_⊢ s) (traverse (map⁺ proj₁ ∘ Lex) ws))


  parse : (ws : Struct Word) → List (Parse ws)
  parse ws with traverse (map⁺ proj₁ ∘ Lex) ws
  parse ws | Γ ∷ Γs = parse′ Γ Γs
    where
      parse′ : (Γ : _) (Γs : List _) → List (foldr₁ _⊎_ (map⁺ (_⊢ s) (Γ ∷ Γs)))
      parse′ Γ       []  = findAll Γ s
      parse′ Γ (Γ′ ∷ Γs) = map inj₁ (findAll Γ s) ++ map inj₂ (parse′ Γ′ Γs)


  ⟦_⟧ : (ws : Struct Word) → List (toAgdaType s)
  ⟦ ws ⟧ with traverse Lex ws
  ⟦ ws ⟧ | Γ ∷ Γs = ⟦⟧-all Γ Γs
    where
      ⟦⟧-one : (Γ : Struct _) → List _
      ⟦⟧-one = λ Γ → map (toAgdaTerm Γ) (findAll (proj₁ <$> Γ) s)
      ⟦⟧-all : (Γ : _) (Γs : List _) → List _
      ⟦⟧-all Γ       []  = ⟦⟧-one Γ
      ⟦⟧-all Γ (Γ′ ∷ Γs) = ⟦⟧-one Γ ++ ⟦⟧-all Γ′ Γs


  infixr 1 ✓_ *_

  ✓_ : Struct Word → Set
  ✓ ws = T (not (null (parse ws)))

  *_ : Struct Word → Set
  * ws = T (null (parse ws))
