------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.Bool                             using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.List                             using (List; _∷_; []; map; foldr; any; null)
open import Data.String                           using (String; _++_; unlines; toList)
open import Function                              using (_$_; _∘_)
open import IO                                    using (IO; writeFile)
open import Logic.ToLaTeX                         using (module ToLaTeX; ToLaTeX)
open import Reflection
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
data Atom : Set where
  N  : Atom
  NP : Atom
  S  : Atom

_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)
N  ≟-Atom N  = yes refl
N  ≟-Atom NP = no (λ ())
N  ≟-Atom S  = no (λ ())
NP ≟-Atom N  = no (λ ())
NP ≟-Atom NP = yes refl
NP ≟-Atom S  = no (λ ())
S  ≟-Atom N  = no (λ ())
S  ≟-Atom NP = no (λ ())
S  ≟-Atom S  = yes refl

⟦_⟧ᵁ : Atom → Set
⟦ N  ⟧ᵁ = Entity → Bool
⟦ NP ⟧ᵁ = Entity
⟦ S  ⟧ᵁ = Bool

AtomToLaTeX : ToLaTeX Atom
AtomToLaTeX = record { toLaTeXPrec = λ _ → toLaTeX }
  where
    toLaTeX : Atom → String
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
  SAID   : Entity → Bool → Bool
  WANTS  : Entity → Bool → Bool


-- * setup tests
infix 1 Assert_

data   TestFailure : Set where
record TestSuccess : Set where

Assert_ : Bool → Set
Assert true  = TestSuccess
Assert false = TestFailure

_∈_ : Term → List Term → Bool
y ∈ xs = any (λ x → ⌊ forgetAbs x ≟ forgetAbs y ⌋) xs
  where
    mutual
      forgetAbs : Term → Term
      forgetAbs (var x args)      = var x (forgetAbsArgs args)
      forgetAbs (con c args)      = con c (forgetAbsArgs args)
      forgetAbs (def f args)      = def f (forgetAbsArgs args)
      forgetAbs (lam v (abs _ x)) = lam v (abs "_" (forgetAbs x))
      forgetAbs (pi (arg i (el s₁ t₁)) (abs _ (el s₂ t₂)))
        = pi (arg i (el s₁ (forgetAbs t₁))) (abs "_" (el s₂ (forgetAbs t₂)))
      forgetAbs t = t

      forgetAbsArgs : List (Arg Term) → List (Arg Term)
      forgetAbsArgs []               = []
      forgetAbsArgs (arg i x ∷ args) = arg i (forgetAbs x) ∷ forgetAbsArgs args


data Proof : Set where
  proof : (file sentence tree term : String) → Proof


mathMode : String → String
mathMode str = if null (toList str) then "" else ("$" ++ str ++ "$")

writeProof : Proof → IO _
writeProof (proof file sentence tree term)
  = writeFile (file ++ ".tex") ∘ unlines
  $ "\\begin{figure}[ht]%"
  ∷ "\\centering%"
  ∷ tree
  ∷ mathMode term
  ∷ ("\\label{" ++ file ++ "}")
  ∷ ("\\caption{``" ++ sentence ++ "''}")
    ∷ "\\end{figure}"
  ∷ []
