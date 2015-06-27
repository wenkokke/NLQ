open import Level
open import Category.Functor
open import Category.Applicative
open import Category.Monad
open import Data.List using (List; _∷_; []; foldr)
open import Data.List.NonEmpty using (List⁺; _∷⁺_; [_]) renaming (foldr to foldr⁺)
open import Data.Maybe


module Data.Traversable where


record RawTraversable {t} (T : Set t → Set t) : Set (suc t) where
  field
    traverse : ∀ {F A B} {{AppF : RawApplicative F}} → (A → F B) → T A → F (T B)
    

open RawTraversable {{...}} public
open RawApplicative {{...}}

instance
  TraversableMaybe : ∀ {a} → RawTraversable {a} Maybe
  TraversableMaybe = record { traverse = λ f m → maybe (λ x → pure just ⊛ f x) (pure nothing) m }
    
  TraversableList : ∀ {a} → RawTraversable {a} List
  TraversableList = record { traverse = λ f xs → foldr (λ x fxs → pure _∷_ ⊛ f x ⊛ fxs) (pure []) xs }
    
  TraversableList⁺ : ∀ {a} → RawTraversable {a} List⁺
  TraversableList⁺ = record { traverse = λ f xs → foldr⁺ (λ x fxs → pure _∷⁺_ ⊛ f x ⊛ fxs) (λ x → [_] <$> f x) xs }
