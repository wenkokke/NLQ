------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)


module Logic.Classical.Ordered.LambekGrishin.Structure.Polarised {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type Atom as T
     using ( Type ; el ; _⇐_ ; _⊗_ ; _⇒_ ; _⇛_ ; _⊕_ ; _⇚_
           ; □_ ; ◇_
           ; ₀_ ; _⁰
           ; ₁_ ; _¹
           ; _⋈ ; ⋈-inv
           ; _∞ ; ∞-inv
           )


infix  10 ·_·
infix  15 [_] ⟨_⟩
infixr 20 _⇒_ _⇐_
infixl 25 _⇚_ _⇛_
infixr 30 _⊗_ _⊕_
infixl 50 _⋈ˢ
infixl 50 _∞ˢ


data Structure : Polarity → Set ℓ where
  ·_· : {p  : Polarity}    (A  : Type)        → Structure p
  [_] : (Γ⁻ : Structure -)                    → Structure -
  ⟨_⟩ : (Γ⁺ : Structure +)                    → Structure +
  ₀_  : (Γ⁻ : Structure +)                    → Structure -
  _⁰  : (Γ⁻ : Structure +)                    → Structure -
  ₁_  : (Γ⁺ : Structure -)                    → Structure +
  _¹  : (Γ⁺ : Structure -)                    → Structure +
  _⊗_ : (Γ⁺ : Structure +) (Δ⁺ : Structure +) → Structure +
  _⇚_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure +
  _⇛_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure +
  _⊕_ : (Γ⁻ : Structure -) (Δ⁻ : Structure -) → Structure -
  _⇒_ : (Γ⁺ : Structure +) (Δ⁻ : Structure -) → Structure -
  _⇐_ : (Γ⁻ : Structure -) (Δ⁺ : Structure +) → Structure -


_⋈ˢ : ∀ {p} → Structure p → Structure p
(· A ·) ⋈ˢ = · A ⋈ ·
([ X ]) ⋈ˢ = [ X ⋈ˢ ]
(⟨ X ⟩) ⋈ˢ = ⟨ X ⋈ˢ ⟩
(₀   X) ⋈ˢ = (X ⋈ˢ)   ⁰
(X   ⁰) ⋈ˢ = ₀       (X ⋈ˢ)
(₁   X) ⋈ˢ = (X ⋈ˢ)   ¹
(X   ¹) ⋈ˢ = ₁       (X ⋈ˢ)
(X ⊗ Y) ⋈ˢ = (Y ⋈ˢ) ⊗ (X ⋈ˢ)
(X ⇒ Y) ⋈ˢ = (Y ⋈ˢ) ⇐ (X ⋈ˢ)
(Y ⇐ X) ⋈ˢ = (X ⋈ˢ) ⇒ (Y ⋈ˢ)
(Y ⊕ X) ⋈ˢ = (X ⋈ˢ) ⊕ (Y ⋈ˢ)
(Y ⇚ X) ⋈ˢ = (X ⋈ˢ) ⇛ (Y ⋈ˢ)
(X ⇛ Y) ⋈ˢ = (Y ⋈ˢ) ⇚ (X ⋈ˢ)


_∞ˢ : ∀ {p} → Structure p → Structure (~ p)
(· A ·) ∞ˢ = · A ∞ ·
([ X ]) ∞ˢ = ⟨ X ∞ˢ ⟩
(⟨ X ⟩) ∞ˢ = [ X ∞ˢ ]
(₀   X) ∞ˢ = (X ∞ˢ)   ¹
(X   ⁰) ∞ˢ = ₁       (X ∞ˢ)
(₁   X) ∞ˢ = (X ∞ˢ)   ⁰
(X   ¹) ∞ˢ = ₀       (X ∞ˢ)
(X ⊗ Y) ∞ˢ = (Y ∞ˢ) ⊕ (X ∞ˢ)
(X ⇒ Y) ∞ˢ = (Y ∞ˢ) ⇚ (X ∞ˢ)
(Y ⇐ X) ∞ˢ = (X ∞ˢ) ⇛ (Y ∞ˢ)
(Y ⊕ X) ∞ˢ = (X ∞ˢ) ⊗ (Y ∞ˢ)
(Y ⇚ X) ∞ˢ = (X ∞ˢ) ⇒ (Y ∞ˢ)
(X ⇛ Y) ∞ˢ = (Y ∞ˢ) ⇐ (X ∞ˢ)


·_·-injective : ∀ {p} {A B} → ·_· {p} A ≡ ·_· {p} B → A ≡ B
·_·-injective refl = refl

[_]-injective : ∀ {X Y} → [ X ] ≡ [ Y ] → X ≡ Y
[_]-injective refl = refl

⟨_⟩-injective : ∀ {X Y} → ⟨ X ⟩ ≡ ⟨ Y ⟩ → X ≡ Y
⟨_⟩-injective refl = refl

₀-injective : ∀ {X Y} → _≡_ { A = Structure - }(₀ X)(₀ Y) → X ≡ Y
₀-injective refl = refl

⁰-injective : ∀ {X Y} → _≡_ { A = Structure - }(X ⁰)(Y ⁰) → X ≡ Y
⁰-injective refl = refl

₁-injective : ∀ {X Y} → _≡_ { A = Structure + }(₁ X)(₁ Y) → X ≡ Y
₁-injective refl = refl

¹-injective : ∀ {X Y} → _≡_ { A = Structure + }(X ¹)(Y ¹) → X ≡ Y
¹-injective refl = refl

⇒-injective : ∀ {X Y Z W} → _≡_ { A = Structure - }(X ⇒ Z)(Y ⇒ W) → X ≡ Y × Z ≡ W
⇒-injective refl = refl , refl

⇐-injective : ∀ {X Y Z W} → _≡_ { A = Structure - }(X ⇐ Z)(Y ⇐ W) → X ≡ Y × Z ≡ W
⇐-injective refl = refl , refl

⇚-injective : ∀ {X Y Z W} → _≡_ { A = Structure + }(X ⇚ Z)(Y ⇚ W) → X ≡ Y × Z ≡ W
⇚-injective refl = refl , refl

⇛-injective : ∀ {X Y Z W} → _≡_ { A = Structure + }(X ⇛ Z)(Y ⇛ W) → X ≡ Y × Z ≡ W
⇛-injective refl = refl , refl

⊗-injective : ∀ {X Y Z W} → _≡_ { A = Structure + }(X ⊗ Z)(Y ⊗ W) → X ≡ Y × Z ≡ W
⊗-injective refl = refl , refl

⊕-injective : ∀ {X Y Z W} → _≡_ { A = Structure - }(X ⊕ Z)(Y ⊕ W) → X ≡ Y × Z ≡ W
⊕-injective refl = refl , refl


⋈ˢ-inv : ∀ {p} (X : Structure p) → (X ⋈ˢ) ⋈ˢ ≡ X
⋈ˢ-inv ·  A  · rewrite ⋈-inv A = refl
⋈ˢ-inv [  X  ] rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv ⟨  X  ⟩ rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (₀   X) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X   ⁰) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (₁   X) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X   ¹) rewrite ⋈ˢ-inv X = refl
⋈ˢ-inv (X ⇒ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇐ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇚ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⇛ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⊗ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ˢ-inv (X ⊕ Y) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl


∞ˢ-inv : ∀ {p} (X : Structure p) → (X ∞ˢ) ∞ˢ ≅ X
∞ˢ-inv { p } ·  A  · rewrite ~-inv p | ∞-inv A = refl
∞ˢ-inv { - } [  X  ] = H.cong  [_] (∞ˢ-inv X)
∞ˢ-inv { + } ⟨  X  ⟩ = H.cong  ⟨_⟩ (∞ˢ-inv X)
∞ˢ-inv { - } (₀   X) = H.cong   ₀_ (∞ˢ-inv X)
∞ˢ-inv { - } (X   ⁰) = H.cong  _⁰  (∞ˢ-inv X)
∞ˢ-inv { + } (₁   X) = H.cong   ₁_ (∞ˢ-inv X)
∞ˢ-inv { + } (X   ¹) = H.cong  _¹  (∞ˢ-inv X)
∞ˢ-inv { + } (X ⊗ Y) = H.cong₂ _⊗_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { - } (X ⇒ Y) = H.cong₂ _⇒_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { - } (X ⇐ Y) = H.cong₂ _⇐_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { - } (X ⊕ Y) = H.cong₂ _⊕_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { + } (X ⇚ Y) = H.cong₂ _⇚_ (∞ˢ-inv X) (∞ˢ-inv Y)
∞ˢ-inv { + } (X ⇛ Y) = H.cong₂ _⇛_ (∞ˢ-inv X) (∞ˢ-inv Y)


module Correct where

  open import Logic.Classical.Ordered.LambekGrishin.Structure Atom
       as Unpolarised hiding (module Structure ; Structure ; _⋈ˢ ; _∞ˢ ; ⋈ˢ-inv ; ∞ˢ-inv)

  data Polarised : Polarity → Unpolarised.Structure → Set ℓ where
    ·_· : ∀ {p}   (A  : Type)                               → Polarised p (· A ·)
    [_] : ∀ {Γ}   (Γ⁻ : Polarised - Γ)                      → Polarised - ([ Γ ])
    ⟨_⟩ : ∀ {Γ}   (Γ⁺ : Polarised + Γ)                      → Polarised + (⟨ Γ ⟩)
    ₀_  : ∀ {Γ}   (Γ⁻ : Polarised + Γ)                      → Polarised - (₀   Γ)
    _⁰  : ∀ {Γ}   (Γ⁻ : Polarised + Γ)                      → Polarised - (Γ   ⁰)
    ₁_  : ∀ {Γ}   (Γ⁺ : Polarised - Γ)                      → Polarised + (₁   Γ)
    _¹  : ∀ {Γ}   (Γ⁺ : Polarised - Γ)                      → Polarised + (Γ   ¹)
    _⊗_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⊗ Δ)
    _⇚_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised + (Γ ⇚ Δ)
    _⇛_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised + (Γ ⇛ Δ)
    _⊕_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⊕ Δ)
    _⇒_ : ∀ {Γ Δ} (Γ⁺ : Polarised + Γ) (Δ⁻ : Polarised - Δ) → Polarised - (Γ ⇒ Δ)
    _⇐_ : ∀ {Γ Δ} (Γ⁻ : Polarised - Γ) (Δ⁺ : Polarised + Δ) → Polarised - (Γ ⇐ Δ)


  forget : ∀ {p} (Γᴾ : Structure p) → Unpolarised.Structure
  forget (· A ·) = · A ·
  forget ([ Γ ]) = [ forget Γ ]
  forget (⟨ Γ ⟩) = ⟨ forget Γ ⟩
  forget (₀   Γ) = ₀ forget Γ
  forget (Γ   ⁰) = forget Γ ⁰
  forget (₁   Γ) = ₁ forget Γ
  forget (Γ   ¹) = forget Γ ¹
  forget (Γ ⊗ Δ) = forget Γ ⊗ forget Δ
  forget (Γ ⇚ Δ) = forget Γ ⇚ forget Δ
  forget (Γ ⇛ Δ) = forget Γ ⇛ forget Δ
  forget (Γ ⊕ Δ) = forget Γ ⊕ forget Δ
  forget (Γ ⇒ Δ) = forget Γ ⇒ forget Δ
  forget (Γ ⇐ Δ) = forget Γ ⇐ forget Δ

  forget-correct : ∀ {p} (Γᴾ : Structure p) → Polarised p (forget Γᴾ)
  forget-correct ·  A  · = · A ·
  forget-correct [  Γ  ] = [ forget-correct Γ ]
  forget-correct ⟨  Γ  ⟩ = ⟨ forget-correct Γ ⟩
  forget-correct (₀   Γ) = ₀ forget-correct Γ
  forget-correct (Γ   ⁰) = forget-correct Γ ⁰
  forget-correct (₁   Γ) = ₁ forget-correct Γ
  forget-correct (Γ   ¹) = forget-correct Γ ¹
  forget-correct (Γ ⊗ Δ) = forget-correct Γ ⊗ forget-correct Δ
  forget-correct (Γ ⇚ Δ) = forget-correct Γ ⇚ forget-correct Δ
  forget-correct (Γ ⇛ Δ) = forget-correct Γ ⇛ forget-correct Δ
  forget-correct (Γ ⊕ Δ) = forget-correct Γ ⊕ forget-correct Δ
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
  · A · ≟-Structure [ Z ] = no (λ ())
  · A · ≟-Structure ⟨ Z ⟩ = no (λ ())
  · A · ≟-Structure (₀ Z) = no (λ ())
  · A · ≟-Structure (Z ⁰) = no (λ ())
  · A · ≟-Structure (₁ Z) = no (λ ())
  · A · ≟-Structure (Z ¹) = no (λ ())
  · A · ≟-Structure Z ⊗ W = no (λ ())
  · A · ≟-Structure Z ⇚ W = no (λ ())
  · A · ≟-Structure Z ⇛ W = no (λ ())
  · A · ≟-Structure Z ⊕ W = no (λ ())
  · A · ≟-Structure Z ⇒ W = no (λ ())
  · A · ≟-Structure Z ⇐ W = no (λ ())

  [ X ] ≟-Structure · B · = no (λ ())
  [ X ] ≟-Structure [ Z ] with (X ≟-Structure Z)
  ... | yes X=Z rewrite X=Z = yes refl
  ... | no  X≠Z = no (X≠Z ∘ [_]-injective)
  [ X ] ≟-Structure (₀ Z) = no (λ ())
  [ X ] ≟-Structure (Z ⁰) = no (λ ())
  [ X ] ≟-Structure Z ⊕ W = no (λ ())
  [ X ] ≟-Structure Z ⇒ W = no (λ ())
  [ X ] ≟-Structure Z ⇐ W = no (λ ())

  ⟨ X ⟩ ≟-Structure · B · = no (λ ())
  ⟨ X ⟩ ≟-Structure ⟨ Z ⟩ with (X ≟-Structure Z)
  ... | yes X=Z rewrite X=Z = yes refl
  ... | no  X≠Z = no (X≠Z ∘ ⟨_⟩-injective)
  ⟨ X ⟩ ≟-Structure (₁ Z) = no (λ ())
  ⟨ X ⟩ ≟-Structure (Z ¹) = no (λ ())
  ⟨ X ⟩ ≟-Structure Z ⊗ W = no (λ ())
  ⟨ X ⟩ ≟-Structure Z ⇚ W = no (λ ())
  ⟨ X ⟩ ≟-Structure Z ⇛ W = no (λ ())

  (₀ X) ≟-Structure · B · = no (λ ())
  (₀ X) ≟-Structure [ Z ] = no (λ ())
  (₀ X) ≟-Structure (₀ Z) with (X ≟-Structure Z)
  ... | yes X=Z rewrite X=Z = yes refl
  ... | no  X≠Z = no (X≠Z ∘ ₀-injective)
  (₀ X) ≟-Structure (Z ⁰) = no (λ ())
  (₀ X) ≟-Structure Z ⊕ W = no (λ ())
  (₀ X) ≟-Structure Z ⇒ W = no (λ ())
  (₀ X) ≟-Structure Z ⇐ W = no (λ ())

  (X ⁰) ≟-Structure · B · = no (λ ())
  (X ⁰) ≟-Structure [ Z ] = no (λ ())
  (X ⁰) ≟-Structure (₀ Z) = no (λ ())
  (X ⁰) ≟-Structure (Z ⁰) with (X ≟-Structure Z)
  ... | yes X=Z rewrite X=Z = yes refl
  ... | no  X≠Z = no (X≠Z ∘ ⁰-injective)
  (X ⁰) ≟-Structure Z ⊕ W = no (λ ())
  (X ⁰) ≟-Structure Z ⇒ W = no (λ ())
  (X ⁰) ≟-Structure Z ⇐ W = no (λ ())

  (₁ X) ≟-Structure · B · = no (λ ())
  (₁ X) ≟-Structure ⟨ Z ⟩ = no (λ ())
  (₁ X) ≟-Structure (₁ Z) with (X ≟-Structure Z)
  ... | yes X=Z rewrite X=Z = yes refl
  ... | no  X≠Z = no (X≠Z ∘ ₁-injective)
  (₁ X) ≟-Structure (Z ¹) = no (λ ())
  (₁ X) ≟-Structure Z ⊗ W = no (λ ())
  (₁ X) ≟-Structure Z ⇚ W = no (λ ())
  (₁ X) ≟-Structure Z ⇛ W = no (λ ())

  (X ¹) ≟-Structure · B · = no (λ ())
  (X ¹) ≟-Structure ⟨ Z ⟩ = no (λ ())
  (X ¹) ≟-Structure (₁ Z) = no (λ ())
  (X ¹) ≟-Structure (Z ¹) with (X ≟-Structure Z)
  ... | yes X=Z rewrite X=Z = yes refl
  ... | no  X≠Z = no (X≠Z ∘ ¹-injective)
  (X ¹) ≟-Structure Z ⊗ W = no (λ ())
  (X ¹) ≟-Structure Z ⇚ W = no (λ ())
  (X ¹) ≟-Structure Z ⇛ W = no (λ ())

  X ⊗ Y ≟-Structure · B · = no (λ ())
  X ⊗ Y ≟-Structure ⟨ Z ⟩ = no (λ ())
  X ⊗ Y ≟-Structure (₁ Z) = no (λ ())
  X ⊗ Y ≟-Structure (Z ¹) = no (λ ())
  X ⊗ Y ≟-Structure Z ⊗ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⊗-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⊗-injective)
  X ⊗ Y ≟-Structure Z ⇚ W = no (λ ())
  X ⊗ Y ≟-Structure Z ⇛ W = no (λ ())

  X ⇚ Y ≟-Structure · B · = no (λ ())
  X ⇚ Y ≟-Structure ⟨ Z ⟩ = no (λ ())
  X ⇚ Y ≟-Structure (₁ Z) = no (λ ())
  X ⇚ Y ≟-Structure (Z ¹) = no (λ ())
  X ⇚ Y ≟-Structure Z ⊗ W = no (λ ())
  X ⇚ Y ≟-Structure Z ⇚ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⇚-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⇚-injective)
  X ⇚ Y ≟-Structure Z ⇛ W = no (λ ())

  X ⇛ Y ≟-Structure · B · = no (λ ())
  X ⇛ Y ≟-Structure ⟨ Z ⟩ = no (λ ())
  X ⇛ Y ≟-Structure (₁ Z) = no (λ ())
  X ⇛ Y ≟-Structure (Z ¹) = no (λ ())
  X ⇛ Y ≟-Structure Z ⊗ W = no (λ ())
  X ⇛ Y ≟-Structure Z ⇚ W = no (λ ())
  X ⇛ Y ≟-Structure Z ⇛ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⇛-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⇛-injective)

  X ⊕ Y ≟-Structure · B · = no (λ ())
  X ⊕ Y ≟-Structure [ Z ] = no (λ ())
  X ⊕ Y ≟-Structure (₀ Z) = no (λ ())
  X ⊕ Y ≟-Structure (Z ⁰) = no (λ ())
  X ⊕ Y ≟-Structure Z ⊕ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⊕-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⊕-injective)
  X ⊕ Y ≟-Structure Z ⇒ W = no (λ ())
  X ⊕ Y ≟-Structure Z ⇐ W = no (λ ())

  X ⇒ Y ≟-Structure · B · = no (λ ())
  X ⇒ Y ≟-Structure [ Z ] = no (λ ())
  X ⇒ Y ≟-Structure (₀ Z) = no (λ ())
  X ⇒ Y ≟-Structure (Z ⁰) = no (λ ())
  X ⇒ Y ≟-Structure Z ⊕ W = no (λ ())
  X ⇒ Y ≟-Structure Z ⇒ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⇒-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⇒-injective)
  X ⇒ Y ≟-Structure Z ⇐ W = no (λ ())

  X ⇐ Y ≟-Structure · B · = no (λ ())
  X ⇐ Y ≟-Structure [ Z ] = no (λ ())
  X ⇐ Y ≟-Structure (₀ Z) = no (λ ())
  X ⇐ Y ≟-Structure (Z ⁰) = no (λ ())
  X ⇐ Y ≟-Structure Z ⊕ W = no (λ ())
  X ⇐ Y ≟-Structure Z ⇒ W = no (λ ())
  X ⇐ Y ≟-Structure Z ⇐ W with (X ≟-Structure Z) | (Y ≟-Structure W)
  ... | yes X=Z | yes Y=W rewrite X=Z | Y=W = yes refl
  ... | no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⇐-injective)
  ... | _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⇐-injective)
