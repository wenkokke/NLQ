------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function.Equivalence using (equivalence)
open import Relation.Binary      using (Rel)


module Logic.Intuitionistic.Ordered.Lambek.SC.Complete {ℓ} (Atom : Set ℓ) where


open import Algebra.ResiduatedAlgebra
open import Logic.Intuitionistic.Ordered.Lambek.Type         Atom as T
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement Atom as SCJ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base      Atom as SCB
open import Logic.Intuitionistic.Ordered.Lambek.SC.Trans     Atom as SCT


private
  _≤_ : Rel Type ℓ
  A ≤ B = NL A ⊢ B


open import Relation.Binary.PartialOrderToEquivalence _≤_ ax′ cut′


isResiduatedAlgebra : IsResiduatedAlgebra _≈_ _≤_ _⊗_ _⇒_ _⇐_
isResiduatedAlgebra = record
  { isPartialOrder = isPartialOrder
  ; residual-⇒     = equivalence r⇒⊗′ r⊗⇒′
  ; residual-⇐     = equivalence r⊗⇐′ r⇐⊗′
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
