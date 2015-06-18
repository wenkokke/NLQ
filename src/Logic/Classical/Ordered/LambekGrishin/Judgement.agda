------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; ≅-to-≡)


module Logic.Classical.Ordered.LambekGrishin.Judgement {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                Atom
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Atom


infix  3  _⊢_ [_]⊢_ _⊢[_]
infixl 50 _⋈ᴶ _∞ᴶ



data Judgement : Set ℓ where
  _⊢_   : Structure + → Structure - → Judgement
  [_]⊢_ : Type        → Structure - → Judgement
  _⊢[_] : Structure + → Type        → Judgement



open import Algebra.FunctionProperties {A = Judgement} _≡_


_⋈ᴶ : Judgement → Judgement
(  X  ⊢  Y  ) ⋈ᴶ = X ⋈ˢ ⊢ Y ⋈ˢ
([ A ]⊢  Y  ) ⋈ᴶ = [ A ⋈ ]⊢ Y ⋈ˢ
(  X  ⊢[ B ]) ⋈ᴶ = X ⋈ˢ ⊢[ B ⋈ ]

_∞ᴶ : Judgement → Judgement
(  X  ⊢  Y  ) ∞ᴶ = Y ∞ˢ ⊢ X ∞ˢ
([ A ]⊢  Y  ) ∞ᴶ = Y ∞ˢ ⊢[ A ∞ ]
(  X  ⊢[ B ]) ∞ᴶ = [ B ∞ ]⊢ X ∞ˢ


⋈ᴶ-inv : Involutive _⋈ᴶ
⋈ᴶ-inv (  X  ⊢  Y  ) rewrite ⋈ˢ-inv X | ⋈ˢ-inv Y = refl
⋈ᴶ-inv ([ A ]⊢  Y  ) rewrite ⋈-inv A | ⋈ˢ-inv Y = refl
⋈ᴶ-inv (  X  ⊢[ B ]) rewrite ⋈ˢ-inv X | ⋈-inv B = refl


∞ᴶ-inv : Involutive _∞ᴶ
∞ᴶ-inv (  X  ⊢  Y  ) rewrite ≅-to-≡ (∞ˢ-inv X) | ≅-to-≡ (∞ˢ-inv Y) = refl
∞ᴶ-inv ([ A ]⊢  Y  ) rewrite ∞-inv A | ≅-to-≡ (∞ˢ-inv Y) = refl
∞ᴶ-inv (  X  ⊢[ B ]) rewrite ≅-to-≡ (∞ˢ-inv X) | ∞-inv B = refl


⊢-injective : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → (Γ₁ ⊢ Γ₂) ≡ (Γ₃ ⊢ Γ₄) → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
⊢-injective refl = refl , refl


[]⊢-injective : ∀ {A B Γ₁ Γ₂} → ([ A ]⊢ Γ₁) ≡ ([ B ]⊢ Γ₂) → A ≡ B × Γ₁ ≡ Γ₂
[]⊢-injective refl = refl , refl


⊢[]-injective : ∀ {A B Γ₁ Γ₂} → (Γ₁ ⊢[ A ]) ≡ (Γ₂ ⊢[ B ]) → Γ₁ ≡ Γ₂ × A ≡ B
⊢[]-injective refl = refl , refl
