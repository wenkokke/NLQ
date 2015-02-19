------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (module DecSetoid; DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ


infix 3 _⊢_ [_]⊢_ _⊢[_]


data Judgement : Set ℓ where
  _⊢_   : Structure + → Structure - → Judgement
  [_]⊢_ : Type        → Structure - → Judgement
  _⊢[_] : Structure + → Type        → Judgement


⊢-injective : ∀ {Γ₁ Γ₂ Γ₃ Γ₄} → (Γ₁ ⊢ Γ₂) ≡ (Γ₃ ⊢ Γ₄) → Γ₁ ≡ Γ₃ × Γ₂ ≡ Γ₄
⊢-injective refl = refl , refl

[]⊢-injective : ∀ {A B Γ₁ Γ₂} → ([ A ]⊢ Γ₁) ≡ ([ B ]⊢ Γ₂) → A ≡ B × Γ₁ ≡ Γ₂
[]⊢-injective refl = refl , refl

⊢[]-injective : ∀ {A B Γ₁ Γ₂} → (Γ₁ ⊢[ A ]) ≡ (Γ₂ ⊢[ B ]) → Γ₁ ≡ Γ₂ × A ≡ B
⊢[]-injective refl = refl , refl
