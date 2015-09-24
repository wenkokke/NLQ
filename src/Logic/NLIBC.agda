------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Relation.Nullary                      using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)


module Logic.NLIBC {ℓ} (Atom : Set ℓ) where


open import Logic.NLIBC.Type              Atom public hiding (module DecEq)
open import Logic.NLIBC.Structure         Atom public hiding (module DecEq)
open import Logic.NLIBC.Structure.Context Atom public
open import Logic.NLIBC.Sequent           Atom public hiding (module DecEq)
open import Logic.NLIBC.Base              Atom public
