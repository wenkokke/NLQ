------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function.Equivalence using (equivalence)
open import Algebra.ResiduatedAlgebra
open import Relation.Binary using (Rel)


module Logic.Lambek.NaturalDeduction.Complete {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.Type                  Univ as T
open import Logic.Lambek.ResMon.Judgement      Univ as NDJ
open import Logic.Lambek.NaturalDeduction.Base Univ as NDB


private
  _≤_ : Rel Type ℓ
  A ≤ B = NL A ⊢ B


open import Relation.Binary.PartialOrderToEquivalence _≤_ id trans′



isResiduatedAlgebra : IsResiduatedAlgebra _≈_ _≤_ _⊗_ _⇒_ _⇐_
isResiduatedAlgebra = record
  { isPartialOrder = isPartialOrder
  ; residual-⇒     = equivalence (λ f → ⇒E id f) (λ f → ⇒I f)
  ; residual-⇐     = equivalence (λ f → ⇐I f) (λ f → ⇐E f id)
  ; ∙-resp-≤       = ⊗I
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
