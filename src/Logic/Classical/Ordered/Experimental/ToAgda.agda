------------------------------------------------------------------------
-- The Lambek Calculus in Agda
-- This file was automatically generated.
------------------------------------------------------------------------


open import Function                                   using (id; _∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂; uncurry)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.Experimental.ToAgda
  {u ℓ} (Univ : Set u) (⊥ : Set ℓ) (⌈_⌉ᵁ : Univ → Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.Experimental.Type                Univ
open import Logic.Classical.Ordered.Experimental.Structure.Polarised Univ
open import Logic.Classical.Ordered.Experimental.Judgement           Univ
open import Logic.Classical.Ordered.Experimental.Base                Univ


infix 3 ¬_

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

deMorgan : {A B : Set ℓ} → (¬ ¬ A) → (¬ ¬ B) → ¬ ¬ (A × B)
deMorgan c₁ c₂ k = c₁ (λ x → c₂ (λ y → k (x , y)))


-- * Call-by-value translation

⌈_⌉ᵀ : Type → Set ℓ
⌈ el  A ⌉ᵀ =      ⌈ A ⌉ᵁ
⌈ ◇   A ⌉ᵀ =      ⌈ A ⌉ᵀ
⌈ □   A ⌉ᵀ =      ⌈ A ⌉ᵀ
⌈ A ⊗ B ⌉ᵀ =   (  ⌈ A ⌉ᵀ ×   ⌈ B ⌉ᵀ)
⌈ A ⇒ B ⌉ᵀ =   (¬ ⌈ B ⌉ᵀ → ¬ ⌈ A ⌉ᵀ)
⌈ B ⇐ A ⌉ᵀ =   (¬ ⌈ B ⌉ᵀ → ¬ ⌈ A ⌉ᵀ)
⌈ B ⊕ A ⌉ᵀ = ¬ (¬ ⌈ B ⌉ᵀ × ¬ ⌈ A ⌉ᵀ)
⌈ B ⇚ A ⌉ᵀ = ¬ (¬ ⌈ A ⌉ᵀ → ¬ ⌈ B ⌉ᵀ)
⌈ A ⇛ B ⌉ᵀ = ¬ (¬ ⌈ A ⌉ᵀ → ¬ ⌈ B ⌉ᵀ)


private
  flatten : ∀ {p} (f : Polarity → Type → Set ℓ) (q : Polarity) (X : Structure p) → Set ℓ
  flatten f + ·  A  · = f + A
  flatten f - ·  A  · = f - A
  flatten f _ [  X  ] = flatten f - X
  flatten f _ ⟨  X  ⟩ = flatten f + X
  flatten f _ (X ⊗ Y) = flatten f + X × flatten f + Y
  flatten f _ (X ⇚ Y) = flatten f + X × flatten f - Y
  flatten f _ (X ⇛ Y) = flatten f - X × flatten f + Y
  flatten f _ (X ⊕ Y) = flatten f - X × flatten f - Y
  flatten f _ (X ⇒ Y) = flatten f + X × flatten f - Y
  flatten f _ (X ⇐ Y) = flatten f - X × flatten f + Y


⌈_⌉ˢ_ : ∀ {p} → Structure p → Polarity → Set ℓ
⌈ X ⌉ˢ q = flatten (λ { + A → ⌈ A ⌉ᵀ ; - A → ¬ ⌈ A ⌉ᵀ }) q X


⌈_⌉ᴶ : Judgement → Set ℓ
⌈   X  ⊢  Y   ⌉ᴶ = ⌈ X ⌉ˢ + → ⌈ Y ⌉ˢ - → ⊥
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
⌈ □ᴸ  f   ⌉ x y = ⌈ f ⌉ x y
⌈ □ᴿ  f   ⌉ x y = ⌈ f ⌉ x y
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
⌈ ⊕ᴸ  f g ⌉ (x , y) k = k (⌈ f ⌉ x , ⌈ g ⌉ y)
⌈ ⊕ᴿ  f   ⌉ x k = k (λ {y → ⌈ f ⌉ x y})
⌈ ⇚ᴸ  f   ⌉ k x = k (λ y z → ⌈ f ⌉ (z , y) x)
⌈ ⇚ᴿ  f g ⌉ (x , y) k = k (λ k → deMorgan (λ k → k (⌈ g ⌉ y)) (⌈ f ⌉ x) (uncurry k))
⌈ ⇛ᴸ  f   ⌉ k x = k (λ y z → ⌈ f ⌉ (y , z) x)
⌈ ⇛ᴿ  f g ⌉ (x , y) k = k (λ k → deMorgan (λ k → k (⌈ g ⌉ x)) (⌈ f ⌉ y) (uncurry k))
⌈ r⇚⊕ f   ⌉ x (y , z) = ⌈ f ⌉ (x , z) y
⌈ r⊕⇚ f   ⌉ (x , y) z = ⌈ f ⌉ x (z , y)
⌈ r⇛⊕ f   ⌉ x (y , z) = ⌈ f ⌉ (y , x) z
⌈ r⊕⇛ f   ⌉ (x , y) z = ⌈ f ⌉ y (x , z)
⌈ d⇛⇐ f   ⌉ (x , y) (z , w) = ⌈ f ⌉ (y , w) (x , z)
⌈ d⇛⇒ f   ⌉ (x , y) (z , w) = ⌈ f ⌉ (z , y) (x , w)
⌈ d⇚⇒ f   ⌉ (x , y) (z , w) = ⌈ f ⌉ (z , x) (w , y)
⌈ d⇚⇐ f   ⌉ (x , y) (z , w) = ⌈ f ⌉ (x , w) (z , y)


CBV : Translation Type (Set ℓ) EXP_ id
CBV = record { ⟦_⟧ᵀ = ⌈_⌉ᵀ ; ⟦_⟧ᴶ = ⌈_⌉ᴶ ; [_]  = ⌈_⌉ }


-- * Call-by-name translation

⌊_⌋ᵀ : Type → Set ℓ
⌊ A ⌋ᵀ = ⌈ A ∞ ⌉ᵀ

⌊_⌋ᴶ : Judgement → Set ℓ
⌊ J ⌋ᴶ = ⌈ J ∞ᴶ ⌉ᴶ

⌊_⌋ : ∀ {J} → EXP J → ⌊ J ⌋ᴶ
⌊ f ⌋ = ⌈ f ∞ᵗ ⌉

CBN : Translation Type (Set ℓ) EXP_ id
CBN = record
  { ⟦_⟧ᵀ = ⌊_⌋ᵀ
  ; ⟦_⟧ᴶ = ⌊_⌋ᴶ
  ; [_]  = ⌊_⌋
  }
