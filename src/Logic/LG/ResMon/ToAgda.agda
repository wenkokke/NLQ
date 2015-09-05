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
open import Logic.LG.ResMon.Sequent Atom
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
  ⌈_⌉L : ∀ {A B} → LG A ⊢ B → ¬ ⌈ B ⌉ → ¬ ⌈ A ⌉
  ⌈ ax       ⌉L k x  = k x
  ⌈ m□  f    ⌉L k x  = ⌈ f ⌉L k x
  ⌈ m◇  f    ⌉L k x  = ⌈ f ⌉L k x
  ⌈ r□◇ f    ⌉L k x  = ⌈ f ⌉L k x
  ⌈ r◇□ f    ⌉L k x  = ⌈ f ⌉L k x
  ⌈ m⁰  f    ⌉L k x  = k (λ y → ⌈ f ⌉R y x)
  ⌈ m₀  f    ⌉L k x  = k (λ y → ⌈ f ⌉R y x)
  ⌈ r⁰₀ f    ⌉L k x  = k (λ y → ⌈ f ⌉L (λ k → k x) y)
  ⌈ r₀⁰ f    ⌉L k x  = k (λ y → ⌈ f ⌉L (λ k → k x) y)
  ⌈ m₁  f    ⌉L k x  = k (λ y → ⌈ f ⌉R y x)
  ⌈ m¹  f    ⌉L k x  = k (λ y → ⌈ f ⌉R y x)
  ⌈ r¹₁ f    ⌉L k x  = ⌈ f ⌉L x k
  ⌈ r₁¹ f    ⌉L k x  = ⌈ f ⌉L x k
  ⌈ r⇒⊗ f    ⌉L   x  =    λ {(y , z) → ⌈ f ⌉L (λ k → k (y , x)) z}
  ⌈ r⊗⇒ f    ⌉L k x  = k (λ {(y , z) → ⌈ f ⌉L z (y , x)})
  ⌈ r⇐⊗ f    ⌉L   x  =    λ {(y , z) → ⌈ f ⌉L (λ k → k (x , z)) y}
  ⌈ r⊗⇐ f    ⌉L k x  = k (λ {(y , z) → ⌈ f ⌉L y (x , z)})
  ⌈ m⊗  f g  ⌉L k    =    λ {(x , y) → deMorgan (⌈ f ⌉R x) (⌈ g ⌉R y) k}
  ⌈ m⇒  f g  ⌉L k k′ = k (λ {(x , y) → deMorgan (⌈ f ⌉R x) (λ k → k  (⌈ g ⌉L y)) k′})
  ⌈ m⇐  f g  ⌉L k k′ = k (λ {(x , y) → deMorgan (λ k → k  (⌈ f ⌉L x)) (⌈ g ⌉R y) k′})
  ⌈ r⇛⊕ f    ⌉L k x  = k (λ {(y , z) → ⌈ f ⌉L z (y , x)})
  ⌈ r⊕⇛ f    ⌉L   x  =    λ {(y , z) → ⌈ f ⌉L (λ k → k (y , x)) z}
  ⌈ r⇚⊕ f    ⌉L k x  = k (λ {(y , z) → ⌈ f ⌉L y (x , z)})
  ⌈ r⊕⇚ f    ⌉L   x  =    λ {(y , z) → ⌈ f ⌉L (λ k → k (x , z)) y}
  ⌈ m⊕  f g  ⌉L k k′ = k (λ {(x , y) → k′ (⌈ f ⌉L x , ⌈ g ⌉L y)})
  ⌈ m⇛  f g  ⌉L k    =    λ {(x , y) → deMorgan (λ k → k (⌈ f ⌉L x)) (⌈ g ⌉R y) k}
  ⌈ m⇚  f g  ⌉L k    =    λ {(x , y) → deMorgan (⌈ f ⌉R x) (λ k → k (⌈ g ⌉L y)) k}
  ⌈ d⇛⇐ f    ⌉L k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉L (λ k → k (x , z)) (y , w)})}
  ⌈ d⇛⇒ f    ⌉L k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉L (λ k → k (x , w)) (z , y)})}
  ⌈ d⇚⇒ f    ⌉L k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉L (λ k → k (w , y)) (z , x)})}
  ⌈ d⇚⇐ f    ⌉L k    =    λ {(x , y) → k (λ {(z , w) → ⌈ f ⌉L (λ k → k (z , y)) (x , w)})}

  ⌈_⌉R : ∀ {A B} → LG A ⊢ B → ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉
  ⌈ ax       ⌉R  x      k  = k x
  ⌈ m□  f    ⌉R  x      k  = ⌈ f ⌉R x k
  ⌈ m◇  f    ⌉R  x      k  = ⌈ f ⌉R x k
  ⌈ r□◇ f    ⌉R  x      k  = ⌈ f ⌉R x k
  ⌈ r◇□ f    ⌉R  x      k  = ⌈ f ⌉R x k
  ⌈ m⁰  f    ⌉R  x      k  = k (λ y → ⌈ f ⌉R y x)
  ⌈ m₀  f    ⌉R  x      k  = k (λ y → ⌈ f ⌉R y x)
  ⌈ r⁰₀ f    ⌉R  x      k  = k (λ y → ⌈ f ⌉R y (λ k → k x))
  ⌈ r₀⁰ f    ⌉R  x      k  = k (λ y → ⌈ f ⌉R y (λ k → k x))
  ⌈ m₁  f    ⌉R  x      k  = k (λ y → ⌈ f ⌉R y x)
  ⌈ m¹  f    ⌉R  x      k  = k (λ y → ⌈ f ⌉R y x)
  ⌈ r¹₁ f    ⌉R  x      k  = ⌈ f ⌉L x k
  ⌈ r₁¹ f    ⌉R  x      k  = ⌈ f ⌉L x k
  ⌈ r⇒⊗ f    ⌉R (x , y) z  = ⌈ f ⌉R y (λ k → k (x , z))
  ⌈ r⊗⇒ f    ⌉R  x      k  = k (λ {(y , z) → ⌈ f ⌉R (y , x) z})
  ⌈ r⇐⊗ f    ⌉R (x , y) z  = ⌈ f ⌉R x (λ k → k (z , y))
  ⌈ r⊗⇐ f    ⌉R  x      k  = k (λ {(y , z) → ⌈ f ⌉R (x , z) y})
  ⌈ m⊗  f g  ⌉R (x , y) k  = deMorgan (⌈ f ⌉R x) (⌈ g ⌉R y) k
  ⌈ m⇒  f g  ⌉R  k′     k  = k (λ {(x , y) → deMorgan (⌈ f ⌉R x) (λ k → k (⌈ g ⌉L y)) k′})
  ⌈ m⇐  f g  ⌉R  k′     k  = k (λ {(x , y) → deMorgan (λ k → k (⌈ f ⌉L x)) (⌈ g ⌉R y) k′})
  ⌈ r⇛⊕ f    ⌉R  x      k  = k (λ {(y , z) → ⌈ f ⌉R (y , x) z})
  ⌈ r⊕⇛ f    ⌉R (x , y) z  = ⌈ f ⌉R y (λ k → k (x , z))
  ⌈ r⊕⇚ f    ⌉R (x , y) z  = ⌈ f ⌉R x (λ k → k (z , y))
  ⌈ r⇚⊕ f    ⌉R  x      k  = k (λ {(y , z) → ⌈ f ⌉R (x , z) y})
  ⌈ m⊕  f g  ⌉R  k′     k  = k (λ {(x , y) → k′ (⌈ f ⌉L x , ⌈ g ⌉L y)})
  ⌈ m⇛  f g  ⌉R (x , y) k  = deMorgan (λ k → k (⌈ f ⌉L x)) (⌈ g ⌉R y) k
  ⌈ m⇚  f g  ⌉R (x , y) k  = deMorgan (⌈ f ⌉R x) (λ k → k (⌈ g ⌉L y)) k
  ⌈ d⇛⇐ f    ⌉R (x , y) k  = k (λ {(z , w) → ⌈ f ⌉R (y , w) (λ k → k (x , z))})
  ⌈ d⇛⇒ f    ⌉R (x , y) k  = k (λ {(z , w) → ⌈ f ⌉R (z , y) (λ k → k (x , w))})
  ⌈ d⇚⇒ f    ⌉R (x , y) k  = k (λ {(z , w) → ⌈ f ⌉R (z , x) (λ k → k (w , y))})
  ⌈ d⇚⇐ f    ⌉R (x , y) k  = k (λ {(z , w) → ⌈ f ⌉R (x , w) (λ k → k (z , y))})


⌈_⌉ʲ : Sequent → Set ℓ
⌈ A ⊢ B ⌉ʲ = ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉

CBV : Translation Type (Set ℓ) LG_ id
CBV = record
  { ⟦_⟧ᵗ = ⌈_⌉
  ; ⟦_⟧ʲ = ⌈_⌉ʲ
  ; [_]  = λ { {_ ⊢ _} f → ⌈_⌉R f}
  }



-- * Call-by-name translation

module _ where -- TODO: HACK! ∞

  ⌊_⌋ : Type → Set ℓ
  ⌊ A ⌋ = ⌈ A ∞ ⌉

  ⌊_⌋L : ∀ {A B} → LG A ⊢ B → (¬ ⌊ A ⌋ → ¬ ⌊ B ⌋)
  ⌊_⌋L = ⌈_⌉L ∘ _∞ᵗ

  ⌊_⌋R : ∀ {A B} → LG A ⊢ B → (⌊ B ⌋ → ¬ ¬ ⌊ A ⌋)
  ⌊_⌋R = ⌈_⌉R ∘ _∞ᵗ

  ⌊_⌋ʲ : Sequent → Set ℓ
  ⌊ A ⊢ B ⌋ʲ = ¬ ⌊ A ⌋ → ¬ ⌊ B ⌋

  CBN : Translation Type (Set ℓ) LG_ id
  CBN = record
    { ⟦_⟧ᵗ = ⌊_⌋
    ; ⟦_⟧ʲ = ⌊_⌋ʲ
    ; [_]  = λ { {_ ⊢ _} f → ⌊_⌋L f}
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
  ⌈_⌉′L : ∀ {A B} → LG A ⊢ B → ¬ ⌈ B ⌉′ → ¬ ⌈ A ⌉′
  ⌈ ax       ⌉′L = λ k x → k x
  ⌈ m□  f    ⌉′L = λ k x → ⌈ f ⌉′L k x
  ⌈ m◇  f    ⌉′L = λ k x → ⌈ f ⌉′L k x
  ⌈ r□◇ f    ⌉′L = λ k x → ⌈ f ⌉′L k x
  ⌈ r◇□ f    ⌉′L = λ k x → ⌈ f ⌉′L k x
  ⌈ m⁰  f    ⌉′L = λ k x → k (λ y → ⌈ f ⌉′R y x)
  ⌈ m₀  f    ⌉′L = λ k x → k (λ y → ⌈ f ⌉′R y x)
  ⌈ r⁰₀ f    ⌉′L = λ k x → k (λ y → ⌈ f ⌉′L (λ k → k x) y)
  ⌈ r₀⁰ f    ⌉′L = λ k x → k (λ y → ⌈ f ⌉′L (λ k → k x) y)
  ⌈ m₁  f    ⌉′L = λ k x → k (λ y → ⌈ f ⌉′R y x)
  ⌈ m¹  f    ⌉′L = λ k x → k (λ y → ⌈ f ⌉′R y x)
  ⌈ r¹₁ f    ⌉′L = λ k x → ⌈ f ⌉′L x k
  ⌈ r₁¹ f    ⌉′L = λ k x → ⌈ f ⌉′L x k
  ⌈ r⇒⊗ f    ⌉′L = λ {x (y , z) → ⌈ f ⌉′L (λ k → k x y) z}
  ⌈ r⊗⇒ f    ⌉′L = λ k x → k (λ y z  → ⌈ f ⌉′L y (z , x))
  ⌈ r⇐⊗ f    ⌉′L = λ {x (y , z) → ⌈ f ⌉′L (λ k → k x z) y}
  ⌈ r⊗⇐ f    ⌉′L = λ k x → k  (λ y z → ⌈ f ⌉′L y (x , z))
  ⌈ m⊗  f g  ⌉′L = λ {k (x , y) → deMorgan (⌈ f ⌉′R x) (⌈ g ⌉′R y) k}
  ⌈ m⇒  f g  ⌉′L = λ k k′ → k (λ x y → deMorgan (λ k → k (⌈ g ⌉′L x)) (⌈ f ⌉′R y) (uncurry k′))
  ⌈ m⇐  f g  ⌉′L = λ k k′ → k (λ x y → deMorgan (λ k → k (⌈ f ⌉′L x)) (⌈ g ⌉′R y) (uncurry k′))
  ⌈ r⇛⊕ f    ⌉′L = λ k x → k (λ {(y , z) → ⌈ f ⌉′L z (λ k → k y x)})
  ⌈ r⊕⇛ f    ⌉′L = λ x k → k (λ y z → ⌈ f ⌉′L (λ k → k (y , x)) z)
  ⌈ r⇚⊕ f    ⌉′L = λ k x → k (λ {(y , z) → ⌈ f ⌉′L y (λ k → k z x)})
  ⌈ r⊕⇚ f    ⌉′L = λ x k → k (λ y z → ⌈ f ⌉′L (λ k → k (x , y)) z)
  ⌈ m⊕  f g  ⌉′L = λ k k′ → k (λ {(x , y) → k′ (⌈ f ⌉′L x , ⌈ g ⌉′L y)})
  ⌈ m⇛  f g  ⌉′L = λ k k′ → k (λ k → k′ (λ x y → deMorgan (λ k → k (⌈ f ⌉′L x)) (⌈ g ⌉′R y) (uncurry k)))
  ⌈ m⇚  f g  ⌉′L = λ k k′ → k (λ k → k′ (λ x y → deMorgan (λ k → k (⌈ g ⌉′L x)) (⌈ f ⌉′R y) (uncurry k)))
  ⌈ d⇛⇐ f    ⌉′L = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′L (λ k → k (z , x)) (w , y)))
  ⌈ d⇛⇒ f    ⌉′L = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′L (λ k → k (z , x)) (y , w)))
  ⌈ d⇚⇒ f    ⌉′L = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′L (λ k → k (x , z)) (y , w)))
  ⌈ d⇚⇐ f    ⌉′L = λ k k′ → k (λ x y → k′ (λ z w → ⌈ f ⌉′L (λ k → k (x , z)) (w , y)))

  ⌈_⌉′R : ∀ {A B} → LG A ⊢ B → ⌈ A ⌉′ → ¬ ¬ ⌈ B ⌉′
  ⌈ ax       ⌉′R = λ x k → k x
  ⌈ m□  f    ⌉′R = λ x k → ⌈ f ⌉′R x k
  ⌈ m◇  f    ⌉′R = λ x k → ⌈ f ⌉′R x k
  ⌈ r□◇ f    ⌉′R = λ x k → ⌈ f ⌉′R x k
  ⌈ r◇□ f    ⌉′R = λ x k → ⌈ f ⌉′R x k
  ⌈ m⁰  f    ⌉′R = λ x k → k (λ y → ⌈ f ⌉′R y x)
  ⌈ m₀  f    ⌉′R = λ x k → k (λ y → ⌈ f ⌉′R y x)
  ⌈ r⁰₀ f    ⌉′R = λ x k → k (λ y → ⌈ f ⌉′R y (λ k → k x))
  ⌈ r₀⁰ f    ⌉′R = λ x k → k (λ y → ⌈ f ⌉′R y (λ k → k x))
  ⌈ m₁  f    ⌉′R = λ x k → k (λ y → ⌈ f ⌉′R y x)
  ⌈ m¹  f    ⌉′R = λ x k → k (λ y → ⌈ f ⌉′R y x)
  ⌈ r¹₁ f    ⌉′R = λ x k → ⌈ f ⌉′L x k
  ⌈ r₁¹ f    ⌉′R = λ x k → ⌈ f ⌉′L x k
  ⌈ r⇒⊗ f    ⌉′R = λ {(x , y) z  → ⌈ f ⌉′R y (λ k → k z x)}
  ⌈ r⊗⇒ f    ⌉′R = λ x k → k (λ y z → ⌈ f ⌉′R (z , x) y)
  ⌈ r⇐⊗ f    ⌉′R = λ {(x , y) z → ⌈ f ⌉′R x (λ k → k z y)}
  ⌈ r⊗⇐ f    ⌉′R = λ x k → k (λ y z → ⌈ f ⌉′R (x , z) y)
  ⌈ m⊗  f g  ⌉′R = λ {(x , y) k  → deMorgan (⌈ f ⌉′R x) (⌈ g ⌉′R y) k}
  ⌈ m⇒  f g  ⌉′R = λ k k′ → k′ (λ x y → deMorgan (λ k → k (⌈ g ⌉′L x)) (⌈ f ⌉′R y) (uncurry k))
  ⌈ m⇐  f g  ⌉′R = λ k k′ → k′ (λ x y → deMorgan (λ k → k (⌈ f ⌉′L x)) (⌈ g ⌉′R y) (uncurry k))
  ⌈ r⇛⊕ f    ⌉′R = λ x k → k (λ {(y , z) → ⌈ f ⌉′R (λ k → k y x) z})
  ⌈ r⊕⇛ f    ⌉′R = λ k x → k (λ y z → ⌈ f ⌉′R z (λ k → k (y , x)))
  ⌈ r⇚⊕ f    ⌉′R = λ x k → k (λ {(y , z) → ⌈ f ⌉′R (λ k → k z x) y})
  ⌈ r⊕⇚ f    ⌉′R = λ k x → k (λ y z → ⌈ f ⌉′R z (λ k → k (x , y)))
  ⌈ m⊕  f g  ⌉′R = λ k k′ → k′ (λ {(x , y) → k (⌈ f ⌉′L x , ⌈ g ⌉′L y)})
  ⌈ m⇛  f g  ⌉′R = λ k k′ → k (λ x y → k′ (λ k′ → deMorgan (λ k → k (⌈ f ⌉′L x)) (⌈ g ⌉′R y) (uncurry k′)))
  ⌈ m⇚  f g  ⌉′R = λ k k′ → k (λ x y → k′ (λ k′ → deMorgan (λ k → k (⌈ g ⌉′L x)) (⌈ f ⌉′R y) (uncurry k′)))
  ⌈ d⇛⇐ f    ⌉′R = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′R (w , y) (λ k → k (z , x))))
  ⌈ d⇛⇒ f    ⌉′R = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′R (y , w) (λ k → k (z , x))))
  ⌈ d⇚⇒ f    ⌉′R = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′R (y , w) (λ k → k (x , z))))
  ⌈ d⇚⇐ f    ⌉′R = λ k k′ → k (λ z w → k′ (λ x y → ⌈ f ⌉′R (w , y) (λ k → k (x , z))))


⌈_⌉′ʲ : Sequent → Set ℓ
⌈ A ⊢ B ⌉′ʲ = ⌈ A ⌉′ → ¬ ¬ ⌈ B ⌉′


CBV′ : Translation Type (Set ℓ) LG_ id
CBV′ = record
  { ⟦_⟧ᵗ = ⌈_⌉′
  ; ⟦_⟧ʲ = ⌈_⌉′ʲ
  ; [_]  = λ { {_ ⊢ _} f → ⌈_⌉′R f}
  }
