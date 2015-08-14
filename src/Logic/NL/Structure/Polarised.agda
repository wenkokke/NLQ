--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Structure/Polarised.agda
--------------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)


module Logic.NL.Structure.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NL.Type Atom as T
     using ( Type ; el
           ; _⇐_ ; _⊗_ ; _⇒_
           ; _⋈ ; ⋈-inv
           )


infix  10 ·_·
infixr 20 _⇒_ _⇐_
infixl 50 _⋈ˢ

data Structure : Polarity → Set ℓ where
  ·_· : {p  : Polarity}    (A  : Type)        → Structure p
  _⊗_ : (Γ⁺ : Structure +) (Δ⁺ : Structure +) → Structure +
  _⇒_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure -
  _⇐_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure -


_⋈ˢ : ∀ {p} → Structure p → Structure p
(· A ·) ⋈ˢ = · A ⋈ ·
(X ⊗ Y) ⋈ˢ = (Y ⋈ˢ) ⊗ (X ⋈ˢ)
(X ⇒ Y) ⋈ˢ = (Y ⋈ˢ) ⇐ (X ⋈ˢ)
(Y ⇐ X) ⋈ˢ = (X ⋈ˢ) ⇒ (Y ⋈ˢ)

·_·-injective : ∀ {p} {A B} → ·_· {p} A ≡ ·_· {p} B → A ≡ B
·_·-injective refl = refl

·⇒·-injective : ∀ {X Y Z W} → _≡_ { A = Structure - }(X ⇒ Z)(Y ⇒ W) → X ≡ Y × Z ≡ W
·⇒·-injective refl = refl , refl

·⇐·-injective : ∀ {X Y Z W} → _≡_ { A = Structure - }(X ⇐ Z)(Y ⇐ W) → X ≡ Y × Z ≡ W
·⇐·-injective refl = refl , refl

·⊗·-injective : ∀ {X Y Z W} → _≡_ { A = Structure + }(X ⊗ Z)(Y ⊗ W) → X ≡ Y × Z ≡ W
·⊗·-injective refl = refl , refl


⋈ˢ-inv : ∀ {p} (X : Structure p) → (X ⋈ˢ) ⋈ˢ ≡ X
⋈ˢ-inv ·  A  · rewrite ⋈-inv A = refl
⋈ˢ-inv (X ⇒ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇐ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⊗ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl

module Correct where

  open import Logic.NL.Structure Atom as Unpolarised
       hiding (module Structure ; Structure
              ; _⋈ˢ  ; ⋈ˢ-inv
              )

  data Polarised : Polarity → Unpolarised.Structure → Set ℓ where
    ·_· : ∀ {p}   (A  : Type)                               → Polarised p (· A ·)
    _⊗_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⊗ Δ)
    _⇒_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⇒ Δ)
    _⇐_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised - (Γ ⇐ Δ)


  forget : ∀ {p} (Γᴾ : Structure p) → Unpolarised.Structure
  forget (· A ·) = · A ·
  forget (Γ ⊗ Δ) = forget Γ ⊗ forget Δ
  forget (Γ ⇒ Δ) = forget Γ ⇒ forget Δ
  forget (Γ ⇐ Δ) = forget Γ ⇐ forget Δ

  forget-correct : ∀ {p} (Γᴾ : Structure p) → Polarised p (forget Γᴾ)
  forget-correct ·  A  · = · A ·
  forget-correct (Γ ⊗ Δ) = forget-correct Γ ⊗ forget-correct Δ
  forget-correct (Γ ⇒ Δ) = forget-correct Γ ⇒ forget-correct Δ
  forget-correct (Γ ⇐ Δ) = forget-correct Γ ⇐ forget-correct Δ


-- Proof that if the given universe has decidable equality, then so do types.
module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where


  module TEQ = T.DecEq _≟-Atom_
  open DecSetoid TEQ.decSetoid using (_≟_)


  infix 4 _≟-Structure_

  _≟-Structure_ : ∀ {p} (X : Structure p) (Y : Structure p) → Dec (X ≡ Y)
  · A · ≟-Structure · B · with (A ≟ B)
  ... | yes A=B rewrite A=B = yes refl
  ... | no  A≠B = no (A≠B ∘ ·_·-injective)
  · A · ≟-Structure Z ⊗ W = no (λ ())
  · A · ≟-Structure Z ⇒ W = no (λ ())
  · A · ≟-Structure Z ⇐ W = no (λ ())

  X ⊗ Y ≟-Structure · B · = no (λ ())
  X ⊗ Y ≟-Structure Z ⊗ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ·⊗·-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ·⊗·-injective)
  X ⇒ Y ≟-Structure · B · = no (λ ())
  X ⇒ Y ≟-Structure Z ⇒ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ·⇒·-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ·⇒·-injective)
  X ⇒ Y ≟-Structure Z ⇐ W = no (λ ())

  X ⇐ Y ≟-Structure · B · = no (λ ())
  X ⇐ Y ≟-Structure Z ⇒ W = no (λ ())
  X ⇐ Y ≟-Structure Z ⇐ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ·⇐·-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ·⇐·-injective)
