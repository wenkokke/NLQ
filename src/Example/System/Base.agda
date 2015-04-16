------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool                             using (Bool; true; false; _∧_; _∨_)
open import Data.List                             using (List; _∷_; []; map; foldr)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)


module Example.System.Base where


-- * setup entities
data Entity : Set where
  john  : Entity
  mary  : Entity
  bill  : Entity

abstract
  forAll : (Entity → Bool) → Bool
  forAll p = foldr (λ x b → b ∧ p x) true (john ∷ mary ∷ bill ∷ [])

  exists : (Entity → Bool) → Bool
  exists p = foldr (λ x b → b ∨ p x) false (john ∷ mary ∷ bill ∷ [])


-- * setup helper function
infixr 4 _⊃_

_⊃_ : Bool → Bool → Bool
true  ⊃ true  = true
true  ⊃ false = false
false ⊃ _     = true


-- * setup atomic formulas
data Univ : Set where
  N  : Univ
  NP : Univ
  S  : Univ

_≟-Univ_ : (A B : Univ) → Dec (A ≡ B)
N  ≟-Univ N  = yes refl
N  ≟-Univ NP = no (λ ())
N  ≟-Univ S  = no (λ ())
NP ≟-Univ N  = no (λ ())
NP ≟-Univ NP = yes refl
NP ≟-Univ S  = no (λ ())
S  ≟-Univ N  = no (λ ())
S  ≟-Univ NP = no (λ ())
S  ≟-Univ S  = yes refl

⟦_⟧ᵁ : Univ → Set
⟦ N  ⟧ᵁ = Entity → Bool
⟦ NP ⟧ᵁ = Entity
⟦ S  ⟧ᵁ = Bool


-- * setup abstract lexicon
abstract
  DUTCH   : Entity → Bool
  DUTCH _ = false

  ENGLISH   : Entity → Bool
  ENGLISH _ = true

  SMILES      : Entity → Bool
  SMILES mary = true
  SMILES john = true
  SMILES _    = false

  LEFT      : Entity → Bool
  LEFT bill = true
  LEFT _    = false

  CHEATS : Entity → Bool
  CHEATS john = true
  CHEATS _    = false

  _TEASES_ : Entity → Entity → Bool
  mary TEASES bill = true
  _    TEASES _    = false

  _LOVES_ : Entity → Entity → Bool
  john LOVES bill = true
  bill LOVES john = true
  mary LOVES john = true
  john LOVES mary = true
  _    LOVES _    = false

  UNICORN   : Entity → Bool
  UNICORN _ = false

  PERSON : Entity → Bool
  PERSON _ = true

  TEACHER       : Entity → Bool
  TEACHER bill  = true
  TEACHER _     = false

postulate
  THINKS : Entity → Bool → Bool
