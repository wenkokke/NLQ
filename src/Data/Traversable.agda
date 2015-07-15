------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.NonEmpty using (List⁺; _∷⁺_; [_]) renaming (foldr to foldr⁺)
open import Data.Maybe
open import Function


module Data.Traversable where


record RawTraversable {t} (T : Set t → Set t) : Set (suc t) where
  field
    traverse   : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → T A → F (T B)

  rawFunctor : RawFunctor T
  rawFunctor = record { _<$>_ = _<$>_ }
    where
      _<$>_ : ∀ {A B} → (A → B) → T A → T B
      _<$>_ f x = traverse {{AppF = idAppF}} f x
        where
          idAppF : ∀ {f} → RawApplicative {f} id
          idAppF = record { pure = id ; _⊛_ = _$_ }

  open RawFunctor rawFunctor public

open RawApplicative {{...}}


instance
  TraversableMaybe : ∀ {a} → RawTraversable {a} Maybe
  TraversableMaybe = record
    { traverse   = λ f m → maybe (λ x → pure just ⊛ f x) (pure nothing) m
    }

  TraversableList : ∀ {a} → RawTraversable {a} List
  TraversableList = record
    { traverse   = λ f xs → foldr (λ x fxs → pure _∷_ ⊛ f x ⊛ fxs) (pure []) xs
    }

  TraversableList⁺ : ∀ {a} → RawTraversable {a} List⁺
  TraversableList⁺ = record
    { traverse   = λ f xs → foldr⁺ (λ x fxs → pure _∷⁺_ ⊛ f x ⊛ fxs) (λ x → [_] <$> f x) xs
    }

open RawTraversable {{...}} public
