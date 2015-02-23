------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function.Equivalence using (equivalence)
open import Relation.Binary      using (Rel)


module Logic.Intuitionistic.Ordered.Lambek.SC.Complete {ℓ} (Univ : Set ℓ) where


open import Algebra.ResiduatedAlgebra
open import Logic.Intuitionistic.Ordered.Lambek.Type         Univ as T
open import Logic.Intuitionistic.Ordered.Lambek.SC.Judgement Univ as SCJ
open import Logic.Intuitionistic.Ordered.Lambek.SC.Base      Univ as SCB
open import Logic.Intuitionistic.Ordered.Lambek.SC.Trans     Univ as SCT


private
  _≤_ : Rel Type ℓ
  A ≤ B = NL A ⊢ B


open import Relation.Binary.PartialOrderToEquivalence _≤_ ax′ trans′


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
