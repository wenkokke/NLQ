------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Proof of completeness of the residuation-monotonicity calculus w.r.t.
-- residuated algebras (or Lambek algebras).
------------------------------------------------------------------------


open import Categories
open import Function using (flip)
open import Function.Equivalence using (equivalence)
open import Algebra.ResiduatedAlgebra
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


module Logic.Lambek.ResMon.Complete {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type             Univ as T
open import Logic.Lambek.ResMon.Judgement Univ as RMJ
open import Logic.Lambek.ResMon.Base      Univ as RMB
open import Logic.Lambek.ResMon.Trans     Univ as RMT


private
  _≤_ : Rel Type ℓ
  A ≤ B = NL A ⊢ B


open import Relation.Binary.PartialOrderToEquivalence _≤_ id′ trans′

-- The proof is simple: show that we can implement the structure of
-- residuated algebras using proofs in the residuation-monotonicity
-- calculus. If we do so, we show that any derivation using a
-- residuated algebra can be translated to a derivation in the
-- residuation-monotonicity calculus.

isResiduatedAlgebra : IsResiduatedAlgebra _≈_ _≤_ _⊗_ _⇒_ _⇐_
isResiduatedAlgebra = record
  { isPartialOrder = isPartialOrder
  ; residual-⇒     = equivalence res-⇒⊗ res-⊗⇒
  ; residual-⇐     = equivalence res-⊗⇐ res-⇐⊗
  ; ∙-resp-≤       = mon-⊗
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
