------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function     using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)


module Logic.LG.ResMon.ToAgda
  {a ℓ} (Atom : Set a) (R : Set ℓ) (⟦_⟧ᴬ : Atom → Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.LG.Type             Atom
open import Logic.LG.ResMon.Judgement Atom
open import Logic.LG.ResMon.Base      Atom


private
  infix 3 ¬_

  ¬_ : Set ℓ → Set ℓ
  ¬ A = A → R

  deMorgan : {A B : Set ℓ} → (¬ ¬ A) → (¬ ¬ B) → ¬ ¬ (A × B)
  deMorgan c₁ c₂ k = c₁ (λ x → c₂ (λ y → k (x , y)))


-- * Call-by-value translation

⌈_⌉ : Type → Set ℓ
⌈ el  A ⌉ =      ⟦ A ⟧ᴬ
⌈ ◇   A ⌉ =      ⌈ A ⌉
⌈ □   A ⌉ =      ⌈ A ⌉
⌈ ₀   A ⌉ = ¬    ⌈ A ⌉
⌈ A   ⁰ ⌉ = ¬    ⌈ A ⌉
⌈ ₁   A ⌉ = ¬    ⌈ A ⌉
⌈ A   ¹ ⌉ = ¬    ⌈ A ⌉
⌈ A ⊗ B ⌉ =   (  ⌈ A ⌉ ×   ⌈ B ⌉)
⌈ A ⇒ B ⌉ = ¬ (  ⌈ A ⌉ × ¬ ⌈ B ⌉)
⌈ B ⇐ A ⌉ = ¬ (¬ ⌈ B ⌉ ×   ⌈ A ⌉)
⌈ B ⊕ A ⌉ = ¬ (¬ ⌈ B ⌉ × ¬ ⌈ A ⌉)
⌈ B ⇚ A ⌉ =   (  ⌈ B ⌉ × ¬ ⌈ A ⌉)
⌈ A ⇛ B ⌉ =   (¬ ⌈ A ⌉ ×   ⌈ B ⌉)


mutual
  ⌈_⌉ᴸ : ∀ {A B} → LG A ⊢ B → ¬ ⌈ B ⌉ → ¬ ⌈ A ⌉
  ⌈ ax       ⌉ᴸ k x  = k x
  ⌈ m□  f    ⌉ᴸ k x  = ⌈ f ⌉ᴸ k x
  ⌈ m◇  f    ⌉ᴸ k x  = ⌈ f ⌉ᴸ k x
  ⌈ r□◇ f    ⌉ᴸ k x  = ⌈ f ⌉ᴸ k x
  ⌈ r◇□ f    ⌉ᴸ k x  = ⌈ f ⌉ᴸ k x
  ⌈ m⁰  f    ⌉ᴸ k x  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ m₀  f    ⌉ᴸ k x  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ r⁰₀ f    ⌉ᴸ k x  = k (λ y → ⌈ f ⌉ᴸ (λ k → k x) y)
  ⌈ r₀⁰ f    ⌉ᴸ k x  = k (λ y → ⌈ f ⌉ᴸ (λ k → k x) y)
  ⌈ m₁  f    ⌉ᴸ k x  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ m¹  f    ⌉ᴸ k x  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ r¹₁ f    ⌉ᴸ k x  = ⌈ f ⌉ᴸ x k
  ⌈ r₁¹ f    ⌉ᴸ k x  = ⌈ f ⌉ᴸ x k
  ⌈ r⇒⊗ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (y , x)) z}
  ⌈ r⊗⇒ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ z (y , x)})
  ⌈ r⇐⊗ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (x , z)) y}
  ⌈ r⊗⇐ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ y (x , z)})
  ⌈ m⊗  f g  ⌉ᴸ k    =    λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (⌈ g ⌉ᴿ y) k}
  ⌈ m⇒  f g  ⌉ᴸ k k′ = k (λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k  (⌈ g ⌉ᴸ y)) k′})
  ⌈ m⇐  f g  ⌉ᴸ k k′ = k (λ {(x , y) → deMorgan (λ k → k  (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k′})
  ⌈ r⇛⊕ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ z (y , x)})
  ⌈ r⊕⇛ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (y , x)) z}
  ⌈ r⇚⊕ f    ⌉ᴸ k x  = k (λ {(y , z) → ⌈ f ⌉ᴸ y (x , z)})
  ⌈ r⊕⇚ f    ⌉ᴸ   x  =    λ {(y , z) → ⌈ f ⌉ᴸ (λ k → k (x , z)) y}
  ⌈ m⊕  f g  ⌉ᴸ k k′ = k (λ {(x , y) → k′ (⌈ f ⌉ᴸ x , ⌈ g ⌉ᴸ y)})
  ⌈ m⇛  f g  ⌉ᴸ k    =    λ {(x , y) → deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k}
  ⌈ m⇚  f g  ⌉ᴸ k    =    λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k}
  ⌈ d⇛⇐ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (x , z)) (y , w)})}
  ⌈ d⇛⇒ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (x , w)) (z , y)})}
  ⌈ d⇚⇒ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (w , y)) (z , x)})}
  ⌈ d⇚⇐ f    ⌉ᴸ k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉ᴸ (λ k → k (z , y)) (x , w)})}

  ⌈_⌉ᴿ : ∀ {A B} → LG A ⊢ B → ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉
  ⌈ ax       ⌉ᴿ  x      k  = k x
  ⌈ m□  f    ⌉ᴿ  x      k  = ⌈ f ⌉ᴿ x k
  ⌈ m◇  f    ⌉ᴿ  x      k  = ⌈ f ⌉ᴿ x k
  ⌈ r□◇ f    ⌉ᴿ  x      k  = ⌈ f ⌉ᴿ x k
  ⌈ r◇□ f    ⌉ᴿ  x      k  = ⌈ f ⌉ᴿ x k
  ⌈ m⁰  f    ⌉ᴿ  x      k  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ m₀  f    ⌉ᴿ  x      k  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ r⁰₀ f    ⌉ᴿ  x      k  = k (λ y → ⌈ f ⌉ᴿ y (λ k → k x))
  ⌈ r₀⁰ f    ⌉ᴿ  x      k  = k (λ y → ⌈ f ⌉ᴿ y (λ k → k x))
  ⌈ m₁  f    ⌉ᴿ  x      k  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ m¹  f    ⌉ᴿ  x      k  = k (λ y → ⌈ f ⌉ᴿ y x)
  ⌈ r¹₁ f    ⌉ᴿ  x      k  = ⌈ f ⌉ᴸ x k
  ⌈ r₁¹ f    ⌉ᴿ  x      k  = ⌈ f ⌉ᴸ x k
  ⌈ r⇒⊗ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ y (λ k → k (x , z))
  ⌈ r⊗⇒ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (y , x) z})
  ⌈ r⇐⊗ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ x (λ k → k (z , y))
  ⌈ r⊗⇐ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (x , z) y})
  ⌈ m⊗  f g  ⌉ᴿ (x , y) k  = deMorgan (⌈ f ⌉ᴿ x) (⌈ g ⌉ᴿ y) k
  ⌈ m⇒  f g  ⌉ᴿ  k′     k  = k (λ {(x , y) → deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k′})
  ⌈ m⇐  f g  ⌉ᴿ  k′     k  = k (λ {(x , y) → deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k′})
  ⌈ r⇛⊕ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (y , x) z})
  ⌈ r⊕⇛ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ y (λ k → k (x , z))
  ⌈ r⊕⇚ f    ⌉ᴿ (x , y) z  = ⌈ f ⌉ᴿ x (λ k → k (z , y))
  ⌈ r⇚⊕ f    ⌉ᴿ  x      k  = k (λ {(y , z) → ⌈ f ⌉ᴿ (x , z) y})
  ⌈ m⊕  f g  ⌉ᴿ  k′     k  = k (λ {(x , y) → k′ (⌈ f ⌉ᴸ x , ⌈ g ⌉ᴸ y)})
  ⌈ m⇛  f g  ⌉ᴿ (x , y) k  = deMorgan (λ k → k (⌈ f ⌉ᴸ x)) (⌈ g ⌉ᴿ y) k
  ⌈ m⇚  f g  ⌉ᴿ (x , y) k  = deMorgan (⌈ f ⌉ᴿ x) (λ k → k (⌈ g ⌉ᴸ y)) k
  ⌈ d⇛⇐ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (y , w) (λ k → k (x , z))})
  ⌈ d⇛⇒ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (z , y) (λ k → k (x , w))})
  ⌈ d⇚⇒ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (z , x) (λ k → k (w , y))})
  ⌈ d⇚⇐ f    ⌉ᴿ (x , y) k  = k (λ {(z , w) → ⌈ f ⌉ᴿ (x , w) (λ k → k (z , y))})


⌈_⌉ᴶ : Judgement → Set ℓ
⌈ A ⊢ B ⌉ᴶ = ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉

CBV : Translation Type (Set ℓ) LG_ id
CBV = record
  { ⟦_⟧ᵀ = ⌈_⌉
  ; ⟦_⟧ᴶ = ⌈_⌉ᴶ
  ; [_]  = λ { {_ ⊢ _} f → ⌈_⌉ᴿ f}
  }



-- * Call-by-name translation

module _ where -- TODO: HACK! ∞

  ⌊_⌋ : Type → Set ℓ
  ⌊ A ⌋ = ⌈ A ∞ ⌉

  ⌊_⌋ᴸ : ∀ {A B} → LG A ⊢ B → (¬ ⌊ A ⌋ → ¬ ⌊ B ⌋)
  ⌊_⌋ᴸ = ⌈_⌉ᴸ ∘ _∞ᵗ

  ⌊_⌋ᴿ : ∀ {A B} → LG A ⊢ B → (⌊ B ⌋ → ¬ ¬ ⌊ A ⌋)
  ⌊_⌋ᴿ = ⌈_⌉ᴿ ∘ _∞ᵗ

  ⌊_⌋ᴶ : Judgement → Set ℓ
  ⌊ A ⊢ B ⌋ᴶ = ¬ ⌊ A ⌋ → ¬ ⌊ B ⌋

  CBN : Translation Type (Set ℓ) LG_ id
  CBN = record
    { ⟦_⟧ᵀ = ⌊_⌋
    ; ⟦_⟧ᴶ = ⌊_⌋ᴶ
    ; [_]  = λ { {_ ⊢ _} f → ⌊_⌋ᴸ f}
    }


-- * Bernardi & Moortgat translation

⌈_⌉′ : Type → Set ℓ
⌈ el  A ⌉′ =      ⟦ A ⟧ᴬ
⌈ ◇   A ⌉′ =      ⌈ A ⌉′
⌈ □   A ⌉′ =      ⌈ A ⌉′
⌈ ₀   A ⌉′ = ¬    ⌈ A ⌉′
⌈ A   ⁰ ⌉′ = ¬    ⌈ A ⌉′
⌈ ₁   A ⌉′ = ¬    ⌈ A ⌉′
⌈ A   ¹ ⌉′ = ¬    ⌈ A ⌉′
⌈ A ⊗ B ⌉′ =   (  ⌈ A ⌉′ ×   ⌈ B ⌉′)
⌈ A ⇒ B ⌉′ =   (¬ ⌈ B ⌉′ → ¬ ⌈ A ⌉′)
⌈ B ⇐ A ⌉′ =   (¬ ⌈ B ⌉′ → ¬ ⌈ A ⌉′)
⌈ B ⊕ A ⌉′ = ¬ (¬ ⌈ B ⌉′ × ¬ ⌈ A ⌉′)
⌈ B ⇚ A ⌉′ = ¬ (¬ ⌈ A ⌉′ → ¬ ⌈ B ⌉′)
⌈ A ⇛ B ⌉′ = ¬ (¬ ⌈ A ⌉′ → ¬ ⌈ B ⌉′)


mutual
  ⌈_⌉′ᴸ : ∀ {A B} → LG A ⊢ B → ¬ ⌈ B ⌉′ → ¬ ⌈ A ⌉′
  ⌈ ax       ⌉′ᴸ = λ k x → k x
  ⌈ m□  f    ⌉′ᴸ = λ k x → ⌈ f ⌉′ᴸ k x
  ⌈ m◇  f    ⌉′ᴸ = λ k x → ⌈ f ⌉′ᴸ k x
  ⌈ r□◇ f    ⌉′ᴸ = λ k x → ⌈ f ⌉′ᴸ k x
  ⌈ r◇□ f    ⌉′ᴸ = λ k x → ⌈ f ⌉′ᴸ k x
  ⌈ m⁰  f    ⌉′ᴸ = λ k x → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ m₀  f    ⌉′ᴸ = λ k x → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ r⁰₀ f    ⌉′ᴸ = λ k x → k (λ y → ⌈ f ⌉′ᴸ (λ k → k x) y)
  ⌈ r₀⁰ f    ⌉′ᴸ = λ k x → k (λ y → ⌈ f ⌉′ᴸ (λ k → k x) y)
  ⌈ m₁  f    ⌉′ᴸ = λ k x → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ m¹  f    ⌉′ᴸ = λ k x → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ r¹₁ f    ⌉′ᴸ = λ k x → ⌈ f ⌉′ᴸ x k
  ⌈ r₁¹ f    ⌉′ᴸ = λ k x → ⌈ f ⌉′ᴸ x k
  ⌈ r⇒⊗ f    ⌉′ᴸ = λ {x (y , z) → ⌈ f ⌉′ᴸ (λ k → k x y) z}
  ⌈ r⊗⇒ f    ⌉′ᴸ = λ k x → k (λ y z  → ⌈ f ⌉′ᴸ y (z , x))
  ⌈ r⇐⊗ f    ⌉′ᴸ = λ {x (y , z) → ⌈ f ⌉′ᴸ (λ k → k x z) y}
  ⌈ r⊗⇐ f    ⌉′ᴸ = λ k x → k  (λ y z → ⌈ f ⌉′ᴸ y (x , z))
  ⌈ m⊗  f g  ⌉′ᴸ = λ {k (x , y) → deMorgan (⌈ f ⌉′ᴿ x) (⌈ g ⌉′ᴿ y) k}
  ⌈ m⇒  f g  ⌉′ᴸ = λ k k′ → k (λ x y → deMorgan (λ k → k (⌈ g ⌉′ᴸ x)) (⌈ f ⌉′ᴿ y) (uncurry k′))
  ⌈ m⇐  f g  ⌉′ᴸ = λ k k′ → k (λ x y → deMorgan (λ k → k (⌈ f ⌉′ᴸ x)) (⌈ g ⌉′ᴿ y) (uncurry k′))
  ⌈ r⇛⊕ f    ⌉′ᴸ = λ k x → k (λ {(y , z) → ⌈ f ⌉′ᴸ z (λ k → k y x)})
  ⌈ r⊕⇛ f    ⌉′ᴸ = λ x k → k (λ y z → ⌈ f ⌉′ᴸ (λ k → k (y , x)) z)
  ⌈ r⇚⊕ f    ⌉′ᴸ = λ k x → k (λ {(y , z) → ⌈ f ⌉′ᴸ y (λ k → k z x)})
  ⌈ r⊕⇚ f    ⌉′ᴸ = λ x k → k (λ y z → ⌈ f ⌉′ᴸ (λ k → k (x , y)) z)
  ⌈ m⊕  f g  ⌉′ᴸ = λ k k′ → k (λ {(x , y) → k′ (⌈ f ⌉′ᴸ x , ⌈ g ⌉′ᴸ y)})
  ⌈ m⇛  f g  ⌉′ᴸ = λ k k′ → k (λ k → k′ (λ x y → deMorgan (λ k → k (⌈ f ⌉′ᴸ x)) (⌈ g ⌉′ᴿ y) (uncurry k)))
  ⌈ m⇚  f g  ⌉′ᴸ = λ k k′ → k (λ k → k′ (λ x y → deMorgan (λ k → k (⌈ g ⌉′ᴸ x)) (⌈ f ⌉′ᴿ y) (uncurry k)))
  ⌈ d⇛⇐ f    ⌉′ᴸ = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′ᴸ (λ k → k (z , x)) (w , y)))
  ⌈ d⇛⇒ f    ⌉′ᴸ = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′ᴸ (λ k → k (z , x)) (y , w)))
  ⌈ d⇚⇒ f    ⌉′ᴸ = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′ᴸ (λ k → k (x , z)) (y , w)))
  ⌈ d⇚⇐ f    ⌉′ᴸ = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′ᴸ (λ k → k (x , z)) (w , y)))

  ⌈_⌉′ᴿ : ∀ {A B} → LG A ⊢ B → ⌈ A ⌉′ → ¬ ¬ ⌈ B ⌉′
  ⌈ ax       ⌉′ᴿ = λ x k → k x
  ⌈ m□  f    ⌉′ᴿ = λ x k → ⌈ f ⌉′ᴿ x k
  ⌈ m◇  f    ⌉′ᴿ = λ x k → ⌈ f ⌉′ᴿ x k
  ⌈ r□◇ f    ⌉′ᴿ = λ x k → ⌈ f ⌉′ᴿ x k
  ⌈ r◇□ f    ⌉′ᴿ = λ x k → ⌈ f ⌉′ᴿ x k
  ⌈ m⁰  f    ⌉′ᴿ = λ x k → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ m₀  f    ⌉′ᴿ = λ x k → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ r⁰₀ f    ⌉′ᴿ = λ x k → k (λ y → ⌈ f ⌉′ᴿ y (λ k → k x))
  ⌈ r₀⁰ f    ⌉′ᴿ = λ x k → k (λ y → ⌈ f ⌉′ᴿ y (λ k → k x))
  ⌈ m₁  f    ⌉′ᴿ = λ x k → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ m¹  f    ⌉′ᴿ = λ x k → k (λ y → ⌈ f ⌉′ᴿ y x)
  ⌈ r¹₁ f    ⌉′ᴿ = λ x k → ⌈ f ⌉′ᴸ x k
  ⌈ r₁¹ f    ⌉′ᴿ = λ x k → ⌈ f ⌉′ᴸ x k
  ⌈ r⇒⊗ f    ⌉′ᴿ = λ {(x , y) z  → ⌈ f ⌉′ᴿ y (λ k → k z x)}
  ⌈ r⊗⇒ f    ⌉′ᴿ = λ x k → k (λ y z → ⌈ f ⌉′ᴿ (z , x) y)
  ⌈ r⇐⊗ f    ⌉′ᴿ = λ {(x , y) z → ⌈ f ⌉′ᴿ x (λ k → k z y)}
  ⌈ r⊗⇐ f    ⌉′ᴿ = λ x k → k (λ y z → ⌈ f ⌉′ᴿ (x , z) y)
  ⌈ m⊗  f g  ⌉′ᴿ = λ {(x , y) k  → deMorgan (⌈ f ⌉′ᴿ x) (⌈ g ⌉′ᴿ y) k}
  ⌈ m⇒  f g  ⌉′ᴿ = λ k k′ → k′ (λ x y → deMorgan (λ k → k (⌈ g ⌉′ᴸ x)) (⌈ f ⌉′ᴿ y) (uncurry k))
  ⌈ m⇐  f g  ⌉′ᴿ = λ k k′ → k′ (λ x y → deMorgan (λ k → k (⌈ f ⌉′ᴸ x)) (⌈ g ⌉′ᴿ y) (uncurry k))
  ⌈ r⇛⊕ f    ⌉′ᴿ = λ x k → k (λ {(y , z) → ⌈ f ⌉′ᴿ (λ k → k y x) z})
  ⌈ r⊕⇛ f    ⌉′ᴿ = λ k x → k (λ y z → ⌈ f ⌉′ᴿ z (λ k → k (y , x)))
  ⌈ r⇚⊕ f    ⌉′ᴿ = λ x k → k (λ {(y , z) → ⌈ f ⌉′ᴿ (λ k → k z x) y})
  ⌈ r⊕⇚ f    ⌉′ᴿ = λ k x → k (λ y z → ⌈ f ⌉′ᴿ z (λ k → k (x , y)))
  ⌈ m⊕  f g  ⌉′ᴿ = λ k k′ → k′ (λ {(x , y) → k (⌈ f ⌉′ᴸ x , ⌈ g ⌉′ᴸ y)})
  ⌈ m⇛  f g  ⌉′ᴿ = λ k k′ → k (λ x y → k′ (λ k′ → deMorgan (λ k → k (⌈ f ⌉′ᴸ x)) (⌈ g ⌉′ᴿ y) (uncurry k′)))
  ⌈ m⇚  f g  ⌉′ᴿ = λ k k′ → k (λ x y → k′ (λ k′ → deMorgan (λ k → k (⌈ g ⌉′ᴸ x)) (⌈ f ⌉′ᴿ y) (uncurry k′)))
  ⌈ d⇛⇐ f    ⌉′ᴿ = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′ᴿ (w , y) (λ k → k (z , x))))
  ⌈ d⇛⇒ f    ⌉′ᴿ = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′ᴿ (y , w) (λ k → k (z , x))))
  ⌈ d⇚⇒ f    ⌉′ᴿ = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′ᴿ (y , w) (λ k → k (x , z))))
  ⌈ d⇚⇐ f    ⌉′ᴿ = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′ᴿ (w , y) (λ k → k (x , z))))


⌈_⌉′ᴶ : Judgement → Set ℓ
⌈ A ⊢ B ⌉′ᴶ = ⌈ A ⌉′ → ¬ ¬ ⌈ B ⌉′


CBV′ : Translation Type (Set ℓ) LG_ id
CBV′ = record
  { ⟦_⟧ᵀ = ⌈_⌉′
  ; ⟦_⟧ᴶ = ⌈_⌉′ᴶ
  ; [_]  = λ { {_ ⊢ _} f → ⌈_⌉′ᴿ f}
  }
