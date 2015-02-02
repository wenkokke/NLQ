open import Data.Product                          using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Logic.Type {ℓ} (Univ : Set ℓ) where


infixr 20 _⇒_
infixl 20 _⇐_
infixl 25 _⇚_
infixr 25 _⇛_
infixr 30 _⊗_
infixr 30 _⊕_


data Type : Set ℓ where

  el  : Univ → Type

  _⇒_ : Type → Type → Type
  _⇐_ : Type → Type → Type
  
  _⇚_ : Type → Type → Type
  _⇛_ : Type → Type → Type

  _⊗_ : Type → Type → Type
  _⊕_ : Type → Type → Type
    
    

-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.

el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl

⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
⇒-injective refl = refl , refl

⇐-injective : ∀ {A B C D} → A ⇐ C ≡ B ⇐ D → A ≡ B × C ≡ D
⇐-injective refl = refl , refl

⇚-injective : ∀ {A B C D} → A ⇚ C ≡ B ⇚ D → A ≡ B × C ≡ D
⇚-injective refl = refl , refl

⇛-injective : ∀ {A B C D} → A ⇛ C ≡ B ⇛ D → A ≡ B × C ≡ D
⇛-injective refl = refl , refl

⊗-injective : ∀ {A B C D} → A ⊗ C ≡ B ⊗ D → A ≡ B × C ≡ D
⊗-injective refl = refl , refl

⊕-injective : ∀ {A B C D} → A ⊕ C ≡ B ⊕ D → A ≡ B × C ≡ D
⊕-injective refl = refl , refl
