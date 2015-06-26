------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Defines a residuated algebra, which I've taken to be:
--
-- (1) a residuated ordered monoid without associativity, or
-- (2) an algebra which adds a partial order and a left and right
--     residuation operation. Congruence of the binary operator ∙
--     results from its compatibility with the partial order ≤.
--
------------------------------------------------------------------------

module Algebra.ResiduatedAlgebra where



open import Level using (Level; suc; _⊔_)
open import Algebra.FunctionProperties as FunctionProperties using (Op₂)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary as Rel using (Rel; _Preserves₂_⟶_⟶_; IsPartialOrder; Poset)
open import Relation.Binary.PartialOrderReasoning as ≤-Reasoning using ()
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalence; _⇔_)
open Equivalence


module ResiduationProperties {a ℓ} {A : Set a} (_≤_ : Rel A ℓ) where

  IsResidualˡ : (⇐ ∙ : Op₂ A) → Set (a ⊔ ℓ)
  IsResidualˡ _⇐_ _∙_ = ∀ {x y z}
    → (((x ∙ y) ≤ z) → (x ≤ (z ⇐ y)))
    × ((x ≤ (z ⇐ y)) → ((x ∙ y) ≤ z))


  IsResidualʳ : (⇒ ∙ : Op₂ A) → Set (a ⊔ ℓ)
  IsResidualʳ _⇒_ _∙_ = ∀ {x y z}
    → ((y ≤ (x ⇒ z)) → ((x ∙ y) ≤ z))
    × (((x ∙ y) ≤ z) → (y ≤ (x ⇒ z)))


record IsResiduatedAlgebra
       {a ℓ₁ ℓ₂} {A : Set a}
       (≈ : Rel A ℓ₁) (≤ : Rel A ℓ₂)
       (∙ : Op₂ A) (⇒ : Op₂ A) (⇐ : Op₂ A) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where

  open FunctionProperties    ≈
  open ResiduationProperties ≤

  field
    isPartialOrder : IsPartialOrder ≈ ≤
    residualʳ      : IsResidualʳ ⇒ ∙
    residualˡ      : IsResidualˡ ⇐ ∙
    ∙-resp-≤       : ∙ Preserves₂ ≤ ⟶ ≤ ⟶ ≤

  open Rel.IsPartialOrder isPartialOrder public
       renaming (refl to ≤-refl; reflexive to ≤-reflexive; trans to ≤-trans)
  open Rel.IsEquivalence isEquivalence public



record ResiduatedAlgebra c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where

  infix  7 _∙_
  infixl 7 _⇐_
  infixr 7 _⇒_
  infix  4 _≈_ _≤_

  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ₁
    _≤_                 : Rel Carrier ℓ₂
    _∙_                 : Op₂ Carrier
    _⇒_                 : Op₂ Carrier
    _⇐_                 : Op₂ Carrier
    isResiduatedAlgebra : IsResiduatedAlgebra _≈_ _≤_ _∙_ _⇒_ _⇐_


  open IsResiduatedAlgebra isResiduatedAlgebra public
  poset : Poset _ _ _
  poset = record { isPartialOrder = isPartialOrder }
  open ≤-Reasoning poset


  ∙-resp-≈ : _∙_ Preserves₂ _≈_ ⟶ _≈_ ⟶ _≈_
  ∙-resp-≈ {x} {y} {u} {v} x≈y u≈v = antisym xu≤yv yv≤xu
    where
      xu≤yv : x ∙ u ≤ y ∙ v
      xu≤yv =
        begin
          x ∙ u ≤⟨ ∙-resp-≤ (≤-reflexive x≈y) (≤-reflexive u≈v) ⟩
          y ∙ v
        ∎
      yv≤xu : y ∙ v ≤ x ∙ u
      yv≤xu =
        begin
          y ∙ v ≤⟨ ∙-resp-≤ (≤-reflexive (sym x≈y)) (≤-reflexive (sym u≈v)) ⟩
          x ∙ u
        ∎


  ⇒-with-≤ : ∀ {x y u v} → x ≤ y → u ≤ v → y ⇒ u ≤ x ⇒ v
  ⇒-with-≤ x≤y u≤v =
    proj₂ residualʳ (≤-trans (proj₂ residualˡ (≤-trans x≤y (
    proj₁ residualˡ          (proj₁ residualʳ ≤-refl)))) u≤v)


  ⇐-with-≤ : ∀ {x y u v} → x ≤ y → u ≤ v → x ⇐ v ≤ y ⇐ u
  ⇐-with-≤  x≤y u≤v =
    proj₁ residualˡ (≤-trans (proj₁ residualʳ (≤-trans u≤v (
    proj₂ residualʳ          (proj₂ residualˡ ≤-refl)))) x≤y)
