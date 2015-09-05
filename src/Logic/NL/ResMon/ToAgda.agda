--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Function     using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)


module Logic.NL.ResMon.ToAgda {ℓ ℓ₂} (Atom : Set ℓ) (⟦_⟧ᴬ : Atom → Set ℓ₂) where


open import Logic.NL.Type             Atom
open import Logic.NL.ResMon.Sequent Atom
open import Logic.NL.ResMon.Base      Atom


⟦_⟧ᵗ : Type → Set ℓ₂
⟦ el  A ⟧ᵗ = ⟦ A ⟧ᴬ
⟦ A ⊗ B ⟧ᵗ = ⟦ A ⟧ᵗ × ⟦ B ⟧ᵗ
⟦ A ⇒ B ⟧ᵗ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ
⟦ B ⇐ A ⟧ᵗ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ


⟦_⟧ʲ : Sequent → Set ℓ₂
⟦ A ⊢ B ⟧ʲ = ⟦ A ⟧ᵗ → ⟦ B ⟧ᵗ


⟦_⟧ : ∀ {J} → NL J → ⟦ J ⟧ʲ
⟦ ax      ⟧  x      = x
⟦ m⊗  f g ⟧ (x , y) = (⟦ f ⟧ x) , (⟦ g ⟧ y)
⟦ m⇒  f g ⟧  h   x  = ⟦ g ⟧ (h (⟦ f ⟧ x))
⟦ m⇐  f g ⟧  h   x  = ⟦ f ⟧ (h (⟦ g ⟧ x))
⟦ r⇒⊗ f   ⟧ (x , y) = ⟦ f ⟧  y   x
⟦ r⊗⇒ f   ⟧  x   y  = ⟦ f ⟧ (y , x)
⟦ r⇐⊗ f   ⟧ (x , y) = ⟦ f ⟧  x   y
⟦ r⊗⇐ f   ⟧  x   y  = ⟦ f ⟧ (x , y)
