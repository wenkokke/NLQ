--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ToAgda.agda
--------------------------------------------------------------------------------


open import Function     using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Binary.PropositionalEquality as P


module Logic.EXP.ToAgda
  {a ℓ} (Atom : Set a) (R : Set ℓ) (⌈_⌉ᵁ : Atom → Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.EXP.Type                Atom
open import Logic.EXP.Structure.Polarised Atom
open import Logic.EXP.Judgement           Atom
open import Logic.EXP.Base                Atom


private
  infix 3 ¬_

  ¬_ : Set ℓ → Set ℓ
  ¬ A = A → R

  deMorgan : {A B : Set ℓ} → (¬ ¬ A) → (¬ ¬ B) → ¬ ¬ (A × B)
  deMorgan c₁ c₂ k = c₁ (λ x → c₂ (λ y → k (x , y)))


-- * Call-by-value translation

private
  ⌈_⌉ᵀ : Type → Set ℓ
  ⌈ el  A ⌉ᵀ =      ⌈ A ⌉ᵁ
  ⌈ ◇   A ⌉ᵀ =      ⌈ A ⌉ᵀ
  ⌈ A ⊗ B ⌉ᵀ =   (  ⌈ A ⌉ᵀ ×   ⌈ B ⌉ᵀ)
  ⌈ A ⇒ B ⌉ᵀ =   (¬ ⌈ B ⌉ᵀ → ¬ ⌈ A ⌉ᵀ)
  ⌈ B ⇐ A ⌉ᵀ =   (¬ ⌈ B ⌉ᵀ → ¬ ⌈ A ⌉ᵀ)
  ⌈_⌉ˢ_ : ∀ {p} → Structure p → Polarity → Set ℓ
  ⌈ X ⌉ˢ q = flatten (λ { + A → ⌈ A ⌉ᵀ ; - A → ¬ ⌈ A ⌉ᵀ }) q X
    where
      flatten : ∀ {p} (f : Polarity → Type → Set ℓ) (q : Polarity) (X : Structure p) → Set ℓ
      flatten f + ·  A  · = f + A
      flatten f - ·  A  · = f - A
      flatten f _ ⟨  X  ⟩ = flatten f + X
      flatten f _ (X ⊗ Y) = flatten f + X × flatten f + Y
      flatten f _ (X ⇒ Y) = flatten f + X × flatten f - Y
      flatten f _ (X ⇐ Y) = flatten f - X × flatten f + Y

  ⌈_⌉ᴶ : Judgement → Set ℓ
  ⌈   X  ⊢  Y   ⌉ᴶ = ⌈ X ⌉ˢ + → ⌈ Y ⌉ˢ - → R
  ⌈ [ A ]⊢  Y   ⌉ᴶ = ⌈ Y ⌉ˢ - →   ¬ ⌈ A ⌉ᵀ
  ⌈   X  ⊢[ B ] ⌉ᴶ = ⌈ X ⌉ˢ + → ¬ ¬ ⌈ B ⌉ᵀ


  ⌈_⌉ : ∀ {J} → EXP J → ⌈ J ⌉ᴶ
  ⌈ ax⁺     ⌉ x y = y x
  ⌈ ax⁻     ⌉ x y = x y
  ⌈ ⇁   f   ⌉ x y = ⌈ f ⌉ x y
  ⌈ ↽   f   ⌉ x y = ⌈ f ⌉ y x
  ⌈ ⇀   f   ⌉ x y = ⌈ f ⌉ x y
  ⌈ ↼   f   ⌉ x y = ⌈ f ⌉ y x
  ⌈ ◇ᴸ  f   ⌉ x y = ⌈ f ⌉ x y
  ⌈ ◇ᴿ  f   ⌉ x y = ⌈ f ⌉ x y
  ⌈ ⊗ᴸ  f   ⌉ x y = ⌈ f ⌉ x y
  ⌈ ⊗ᴿ  f g ⌉ (x , y) k = deMorgan (⌈ f ⌉ x) (⌈ g ⌉ y) k
  ⌈ ⇒ᴸ  f g ⌉ (x , y) k = deMorgan (λ k → k (⌈ g ⌉ y)) (⌈ f ⌉ x) (uncurry k)
  ⌈ ⇒ᴿ  f   ⌉ x k = k (λ y z → ⌈ f ⌉ x (z , y))
  ⌈ ⇐ᴸ  f g ⌉ (x , y) k = deMorgan (λ k → k (⌈ g ⌉ x)) (⌈ f ⌉ y) (uncurry k)
  ⌈ ⇐ᴿ  f   ⌉ x k = k (λ y z → ⌈ f ⌉ x (y , z))
  ⌈ r⇒⊗ f   ⌉ (x , y) z = ⌈ f ⌉ y (x , z)
  ⌈ r⊗⇒ f   ⌉ x (y , z) = ⌈ f ⌉ (y , x) z
  ⌈ r⇐⊗ f   ⌉ (x , y) z = ⌈ f ⌉ x (z , y)
  ⌈ r⊗⇐ f   ⌉ x (y , z) = ⌈ f ⌉ (x , z) y
CBV : Translation Type (Set ℓ) EXP_ id
CBV = record { ⟦_⟧ᵀ = ⌈_⌉ᵀ ; ⟦_⟧ᴶ = ⌈_⌉ᴶ ; [_]  = ⌈_⌉ }
