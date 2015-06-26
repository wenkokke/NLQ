------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Proof of completeness of the residuation-monotonicity calculus w.r.t.
-- residuated algebras (or Lambek algebras).
------------------------------------------------------------------------


open import Function                                   using (flip)
open import Function.Equivalence                       using (equivalence)
open import Data.Product                               using (_,_)
open import Relation.Binary                            using (Rel)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Intuitionistic.Ordered.Lambek.ResMon.Complete {ℓ} (Atom : Set ℓ) where


open import Algebra.ResiduatedAlgebra
open import Logic.Intuitionistic.Ordered.Lambek.Type             Atom
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Judgement Atom
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Base      Atom
open import Logic.Intuitionistic.Ordered.Lambek.ResMon.Trans     Atom


private
  _≤_ : Rel Type ℓ
  A ≤ B = NL A ⊢ B


open import Relation.Binary.PartialOrderToEquivalence _≤_ ax′ cut′

-- The proof is simple: show that we can implement the structure of
-- residuated algebras using proofs in the residuation-monotonicity
-- calculus. If we do so, we show that any derivation using a
-- residuated algebra can be translated to a derivation in the
-- residuation-monotonicity calculus.

isResiduatedAlgebra : IsResiduatedAlgebra _≈_ _≤_ _⊗_ _⇒_ _⇐_
isResiduatedAlgebra = record
  { isPartialOrder = isPartialOrder
  ; residualʳ      = r⇒⊗ , r⊗⇒
  ; residualˡ      = r⊗⇐ , r⇐⊗
  ; ∙-resp-≤       = m⊗
  }


resiuatedAlgebra : ResiduatedAlgebra _ _ _
resiuatedAlgebra = record
  { Carrier             = Type
  ; _≈_                 = _≈_
  ; _≤_                 = _≤_
  ; _∙_                 = _⊗_
  ; _⇒_                 = _⇒_
  ; _⇐_                 = _⇐_
  ; isResiduatedAlgebra = isResiduatedAlgebra
  }
