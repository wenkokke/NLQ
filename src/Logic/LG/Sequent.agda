------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; ≅-to-≡)


module Logic.LG.Sequent {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity hiding (decSetoid)
open import Logic.LG.Type Atom                as T hiding (module DecEq)
open import Logic.LG.Structure.Polarised Atom as S hiding (module DecEq)


infix  3  _⊢_ [_]⊢_ _⊢[_]
infixl 50 _⋈ʲ
infixl 50 _∞ʲ



data Sequent : Set ℓ where
  _⊢_   : Structure + → Structure - → Sequent
  [_]⊢_ : Type        → Structure - → Sequent
  _⊢[_] : Structure + → Type        → Sequent



open import Algebra.FunctionProperties {A = Sequent} _≡_


_⋈ʲ : Sequent → Sequent
(  X  ⊢  Y  ) ⋈ʲ = X ⋈ˢ ⊢ Y ⋈ˢ
([ A ]⊢  Y  ) ⋈ʲ = [ A ⋈ ]⊢ Y ⋈ˢ
(  X  ⊢[ B ]) ⋈ʲ = X ⋈ˢ ⊢[ B ⋈ ]

_∞ʲ : Sequent → Sequent
(  X  ⊢  Y  ) ∞ʲ = Y ∞ˢ ⊢ X ∞ˢ
([ A ]⊢  Y  ) ∞ʲ = Y ∞ˢ ⊢[ A ∞ ]
(  X  ⊢[ B ]) ∞ʲ = [ B ∞ ]⊢ X ∞ˢ


⋈ʲ-inv : Involutive _⋈ʲ
⋈ʲ-inv (  X  ⊢  Y  ) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ʲ-inv ([ A ]⊢  Y  ) rewrite ⋈-inv A | ⋈ˢ-inv Y = refl
⋈ʲ-inv (  X  ⊢[ B ]) rewrite ⋈ˢ-inv X | ⋈-inv B = refl


∞ʲ-inv : Involutive _∞ʲ
∞ʲ-inv (  X  ⊢  Y  ) rewrite ≅-to-≡ (∞ˢ-inv X) | ≅-to-≡ (∞ˢ-inv Y) = refl
∞ʲ-inv ([ A ]⊢  Y  ) rewrite ∞-inv A | ≅-to-≡ (∞ˢ-inv Y) = refl
∞ʲ-inv (  X  ⊢[ B ]) rewrite ≅-to-≡ (∞ˢ-inv X) | ∞-inv B = refl


⊢-injective : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → (Γ₁ ⊢ Γ₂) ≡ (Γ₃ ⊢ Γ₄) → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
⊢-injective refl = refl , refl


[]⊢-injective : ∀ {A B Γ₁ Γ₂} → ([ A ]⊢ Γ₁) ≡ ([ B ]⊢ Γ₂) → A ≡ B × Γ₁ ≡ Γ₂
[]⊢-injective refl = refl , refl


⊢[]-injective : ∀ {A B Γ₁ Γ₂} → (Γ₁ ⊢[ A ]) ≡ (Γ₂ ⊢[ B ]) → Γ₁ ≡ Γ₂ × A ≡ B
⊢[]-injective refl = refl , refl


module DecEq (_≟-Atom_ : (A B : Atom) → Dec (A ≡ B)) where


  open module TEQ = T.DecEq _≟-Atom_ using (_≟-Type_)
  open module SEQ = S.DecEq _≟-Atom_ using (_≟-Structure_)


  _≟-Sequent_ : (I J : Sequent) → Dec (I ≡ J)
  (  X  ⊢  Y  ) ≟-Sequent (  Z  ⊢  W  ) with X ≟-Structure Z | Y ≟-Structure W
  ...| yes X=Z | yes Y=W = yes (P.cong₂ _⊢_ X=Z Y=W)
  ...| no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⊢-injective)
  ...| _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ ⊢-injective)
  (  X  ⊢  Y  ) ≟-Sequent ([ C ]⊢  W  ) = no (λ ())
  (  X  ⊢  Y  ) ≟-Sequent (  Z  ⊢[ D ]) = no (λ ())
  ([ A ]⊢  Y  ) ≟-Sequent (  Z  ⊢  W  ) = no (λ ())
  ([ A ]⊢  Y  ) ≟-Sequent ([ C ]⊢  W  ) with A ≟-Type C | Y ≟-Structure W
  ...| yes A=C | yes Y=W = yes (P.cong₂ [_]⊢_ A=C Y=W)
  ...| no  A≠C | _       = no (A≠C ∘ proj₁ ∘ []⊢-injective)
  ...| _       | no  Y≠W = no (Y≠W ∘ proj₂ ∘ []⊢-injective)
  ([ A ]⊢  Y  ) ≟-Sequent (  Z  ⊢[ D ]) = no (λ ())
  (  X  ⊢[ B ]) ≟-Sequent (  Z  ⊢  W  ) = no (λ ())
  (  X  ⊢[ B ]) ≟-Sequent ([ C ]⊢  W  ) = no (λ ())
  (  X  ⊢[ B ]) ≟-Sequent (  Z  ⊢[ D ]) with X ≟-Structure Z | B ≟-Type D
  ...| yes X=Z | yes B=D = yes (P.cong₂ _⊢[_] X=Z B=D)
  ...| no  X≠Z | _       = no (X≠Z ∘ proj₁ ∘ ⊢[]-injective)
  ...| _       | no  B≠D = no (B≠D ∘ proj₂ ∘ ⊢[]-injective)

  decSetoid : DecSetoid _ _
  decSetoid = P.decSetoid _≟-Sequent_
