------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                 using (zero)
open import Data.Product                          using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Traversable                      using (module RawTraversable)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Reflection                            using (Name)


module Example.System.NL where


open import Example.System.Base public
open import Logic.Grammar public
open import Logic.Polarity
open import Logic.Translation
open import Logic.NL.Type Atom as T hiding (module DecEq) public
open import Logic.NL.Sequent Atom as J hiding (module DecEq) public
open import Logic.NL.Structure.Polarised Atom public
open import Logic.NL.Base Atom public
open import Logic.NL.ProofSearch Atom _≟-Atom_  public
open import Logic.NL.ToAgda Atom Bool ⟦_⟧ᴬ public


Structure⁺ = Structure +
Structure⁻ = Structure -
