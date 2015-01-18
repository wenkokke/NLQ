------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (flip; _∘_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Type {ℓ} (Univ : Set ℓ) where


infixr 30 _⊗_
infixr 20 _⇛_
infixr 20 _⇒_
data Type : Set ℓ where
  el   : Univ → Type
  _⊗_  : Type → Type → Type
  _⇛_  : Type → Type → Type
  _⇒_  : Type → Type → Type


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.

el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl

⊗-injective : ∀ {A B C D} → A ⊗ C ≡ B ⊗ D → A ≡ B × C ≡ D
⊗-injective refl = refl , refl

⇒-injective : ∀ {A B C D} → A ⇒ C ≡ B ⇒ D → A ≡ B × C ≡ D
⇒-injective refl = refl , refl

⇛-injective : ∀ {A B C D} → A ⇛ C ≡ B ⇛ D → A ≡ B × C ≡ D
⇛-injective refl = refl , refl

-- Proof that if the given universe has decidable equality, then so do types.
module DecEq
       (_≟-Univ_ : (A B : Univ) → Dec (A ≡ B))
       where

  infix 4 _≟-Type_

  _≟-Type_ : (A B : Type) → Dec (A ≡ B)
  el A  ≟-Type el C  with (A ≟-Univ C)
  ... | yes A≡C rewrite A≡C = yes refl
  ... | no  A≢C = no (A≢C ∘ el-injective)
  el A  ≟-Type C ⊗ D = no (λ ())
  el A  ≟-Type C ⇛ D = no (λ ())
  el A  ≟-Type C ⇒ D = no (λ ())
  A ⊗ B ≟-Type el C  = no (λ ())
  A ⇛ B ≟-Type el C  = no (λ ())
  A ⇒ B ≟-Type el C  = no (λ ())
  A ⊗ B ≟-Type C ⊗ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A≡C | yes B≡D rewrite A≡C | B≡D = yes refl     -- doink
  ... | no  A≢C | _       = no (A≢C ∘ proj₁ ∘ ⊗-injective) -- doink
  ... | _       | no  B≢D = no (B≢D ∘ proj₂ ∘ ⊗-injective) -- doink
  A ⊗ B ≟-Type C ⇛ D = no (λ ())
  A ⊗ B ≟-Type C ⇒ D = no (λ ())
  A ⇛ B ≟-Type C ⊗ D = no (λ ())
  A ⇛ B ≟-Type C ⇛ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A≡C | yes B≡D rewrite A≡C | B≡D = yes refl
  ... | no  A≢C | _       = no (A≢C ∘ proj₁ ∘ ⇛-injective)
  ... | _       | no  B≢D = no (B≢D ∘ proj₂ ∘ ⇛-injective)
  A ⇛ B ≟-Type C ⇒ D = no (λ ())
  A ⇒ B ≟-Type C ⊗ D = no (λ ())
  A ⇒ B ≟-Type C ⇛ D = no (λ ())
  A ⇒ B ≟-Type C ⇒ D with (A ≟-Type C) | (B ≟-Type D)
  ... | yes A≡C | yes B≡D rewrite A≡C | B≡D = yes refl
  ... | no  A≢C | _       = no (A≢C ∘ proj₁ ∘ ⇒-injective)
  ... | _       | no  B≢D = no (B≢D ∘ proj₂ ∘ ⇒-injective)


  instance
    decSetoid : DecSetoid _ _
    decSetoid = P.decSetoid _≟-Type_
