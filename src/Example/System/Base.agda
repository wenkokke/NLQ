------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool                             using (Bool; true; false; _∧_; _∨_)
open import Data.List                             using (List; _∷_; []; map; foldr; any)
open import Data.String                           using (String; _++_; unlines)
open import Function                              using (_$_; _∘_)
open import IO                                    using (IO; writeFile)
open import Logic.ToLaTeX                         using (module ToLaTeX; ToLaTeX)
open import Reflection                            using (Term; _≟_)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
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

UnivToLaTeX : ToLaTeX Univ
UnivToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX }
  where
    toLaTeX : Univ → String
    toLaTeX N  = "n"
    toLaTeX NP = "np"
    toLaTeX S  = "s"


-- * setup abstract lexicon
postulate
  DUTCH   : Entity → Bool
  ENGLISH : Entity → Bool
  SMILES  : Entity → Bool
  LEFT    : Entity → Bool
  CHEATS  : Entity → Bool
  TEASES  : Entity → Entity → Bool
  LOVES   : Entity → Entity → Bool
  UNICORN : Entity → Bool
  PERSON  : Entity → Bool
  TEACHER : Entity → Bool
  THINKS  : Entity → Bool → Bool


-- * setup tests
infix 1 Assert_

data   TestFailure : Set where
record TestSuccess : Set where

Assert_ : Bool → Set
Assert true  = TestSuccess
Assert false = TestFailure

_∈_ : Term → List Term → Bool
y ∈ xs = any (λ x → ⌊ x ≟ y ⌋) xs


data Proof : Set where
  proof : (file sentence tree term : String) → Proof


writeProof : Proof → IO _
writeProof (proof file sentence tree term)
  = writeFile (file ++ ".tex") ∘ unlines
  $ "\\begin{figure}"
  ∷ "\\centering"
  ∷ tree
  ∷ ("$" ++ term ++ "$")
  ∷ ("\\label{" ++ file ++ "}")
  ∷ ("\\caption{\"" ++ sentence ++ "\"}")
    ∷ "\\end{figure}"
  ∷ []
