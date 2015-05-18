------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function     using (id)
open import Data.Product using (_×_; _,_; proj₁; proj₂)


module Logic.Classical.Ordered.LambekGrishin.ResMon.ToAgda
       {u ℓ} (Univ : Set u) (⊥ : Set ℓ) (⟦_⟧ᵁ : Univ → Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.Type             Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Univ


infix 3 ¬_

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

⌈_⌉ : Type → Set ℓ
⌈ el  A ⌉ =      ⟦ A ⟧ᵁ
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

⌊_⌋ : Type → Set ℓ
⌊ A ⌋ = ⌈ A ∞ ⌉


A⟶¬¬A : ∀ {A} → A → ¬ ¬ A
A⟶¬¬A x k = k x

¬¬A×¬¬B⟶¬¬[A×B] : ∀ {A B} → (¬ ¬ A) × (¬ ¬ B) → ¬ ¬ (A × B)
¬¬A×¬¬B⟶¬¬[A×B] (ca , cb) kab =
  ca (λ a → cb (λ b → kab (a , b)))

¬¬[A×B]⟶¬¬A×¬¬B  : ∀ {A B} → ¬ ¬ (A × B) → (¬ ¬ A) × (¬ ¬ B)
¬¬[A×B]⟶¬¬A×¬¬B cab =
  (λ ka → cab (λ {(a , _) → ka a})) , (λ kb → cab (λ {(_ , b) → kb b}))


mutual
  cbvᴸ : ∀ {A B} → LG A ⊢ B → (¬ ⌈ B ⌉ → ¬ ⌈ A ⌉)
  cbvᴸ  ax       k  x      = k x
  cbvᴸ (m◇  f)   k  x      = cbvᴿ f x k
  cbvᴸ (m□  f)   k  x      = cbvᴿ f x k
  cbvᴸ (r◇□ f)   k  x      = cbvᴿ f x k
  cbvᴸ (r□◇ f)   k  x      = cbvᴿ f x k
  cbvᴸ (m⁰  f)   k  x      = k (λ y → cbvᴿ f y x)
  cbvᴸ (m₀  f)   k  x      = k (λ y → cbvᴿ f y x)
  cbvᴸ (r⁰₀ f)   k  x      = k (λ y → cbvᴸ f (A⟶¬¬A x) y)
  cbvᴸ (r₀⁰ f)   k  x      = k (λ y → cbvᴸ f (A⟶¬¬A x) y)
  cbvᴸ (m₁  f)   k  x      = k (λ y → cbvᴿ f y x)
  cbvᴸ (m¹  f)   k  x      = k (λ y → cbvᴿ f y x)
  cbvᴸ (r¹₁ f)   k  x      = cbvᴸ f x k
  cbvᴸ (r₁¹ f)   k  x      = cbvᴸ f x k
  cbvᴸ (m⊗  f g) k (x , y) = ¬¬A×¬¬B⟶¬¬[A×B] (cbvᴿ f x , cbvᴿ g y) k
  cbvᴸ (m⇒  f g) k  k′     = k (λ {(x , y) → ¬¬A×¬¬B⟶¬¬[A×B] (cbvᴿ f x , A⟶¬¬A (cbvᴸ g y)) k′})
  cbvᴸ (m⇐  f g) k  k′     = k (λ {(x , y) → ¬¬A×¬¬B⟶¬¬[A×B] (A⟶¬¬A (cbvᴸ f x) , cbvᴿ g y) k′})
  cbvᴸ (r⇒⊗ f)   k (x , y) = cbvᴸ f (A⟶¬¬A (x , k)) y
  cbvᴸ (r⊗⇒ f)   k  x      = k (λ {(y , z) → cbvᴸ f z (y , x)})
  cbvᴸ (r⇐⊗ f)   k (x , y) = cbvᴸ f (A⟶¬¬A (k , y)) x
  cbvᴸ (r⊗⇐ f)   k  x      = k (λ {(y , z) → cbvᴸ f y (x , z)})
  cbvᴸ (m⊕  f g) k  k′     = k (λ {(x , y) → k′ (cbvᴸ f x , cbvᴸ g y)})
  cbvᴸ (m⇛  f g) k (x , y) = ¬¬A×¬¬B⟶¬¬[A×B] ((A⟶¬¬A (cbvᴸ f x)) , cbvᴿ g y) k
  cbvᴸ (m⇚  f g) k (x , y) = ¬¬A×¬¬B⟶¬¬[A×B] (cbvᴿ f x , (A⟶¬¬A (cbvᴸ g y))) k
  cbvᴸ (r⇛⊕ f)   k  x      = k (λ {(y , z) → cbvᴸ f z (y , x)})
  cbvᴸ (r⊕⇛ f)   k (x , y) = cbvᴸ f (A⟶¬¬A (x , k)) y
  cbvᴸ (r⊕⇚ f)   k (x , y) = cbvᴸ f (A⟶¬¬A (k , y)) x
  cbvᴸ (r⇚⊕ f)   k  x      = k (λ {(y , z) → cbvᴸ f y (x , z)})
  cbvᴸ (d⇛⇐ f)   k (x , y) = k (λ {(z , w) → cbvᴸ f (A⟶¬¬A (x , z)) (y , w)})
  cbvᴸ (d⇛⇒ f)   k (x , y) = k (λ {(z , w) → cbvᴸ f (A⟶¬¬A (x , w)) (z , y)})
  cbvᴸ (d⇚⇒ f)   k (x , y) = k (λ {(z , w) → cbvᴸ f (A⟶¬¬A (w , y)) (z , x)})
  cbvᴸ (d⇚⇐ f)   k (x , y) = k (λ {(z , w) → cbvᴸ f (A⟶¬¬A (z , y)) (x , w)})

  cbvᴿ : ∀ {A B} → LG A ⊢ B → (⌈ A ⌉ → ¬ ¬ ⌈ B ⌉)
  cbvᴿ  ax        x      k  = k x
  cbvᴿ (m◇  f)    x      k  = cbvᴿ f x k
  cbvᴿ (m□  f)    x      k  = cbvᴿ f x k
  cbvᴿ (r◇□ f)    x      k  = cbvᴿ f x k
  cbvᴿ (r□◇ f)    x      k  = cbvᴿ f x k
  cbvᴿ (m⁰  f)    x      k  = k (λ y → cbvᴸ f x y)
  cbvᴿ (m₀  f)    x      k  = k (λ y → cbvᴸ f x y)
  cbvᴿ (r⁰₀ f)    x      k  = k (λ y → cbvᴸ f (A⟶¬¬A x) y)
  cbvᴿ (r₀⁰ f)    x      k  = k (λ y → cbvᴸ f (A⟶¬¬A x) y)
  cbvᴿ (m₁  f)    x      k  = k (λ y → cbvᴸ f x y)
  cbvᴿ (m¹  f)    x      k  = k (λ y → cbvᴸ f x y)
  cbvᴿ (r¹₁ f)    x      k  = cbvᴸ f x k
  cbvᴿ (r₁¹ f)    x      k  = cbvᴸ f x k
  cbvᴿ (m⊗  f g) (x , y) k  = ¬¬A×¬¬B⟶¬¬[A×B] (cbvᴿ f x , cbvᴿ g y) k
  cbvᴿ (m⇒  f g)  k      k′ = k′ (λ {(x , y) → ¬¬A×¬¬B⟶¬¬[A×B] (cbvᴿ f x , A⟶¬¬A (cbvᴸ g y)) k})
  cbvᴿ (m⇐  f g)  k      k′ = k′ (λ {(x , y) → ¬¬A×¬¬B⟶¬¬[A×B] (A⟶¬¬A (cbvᴸ f x) , cbvᴿ g y) k})
  cbvᴿ (r⇒⊗ f)   (x , y) k  = cbvᴿ f y (A⟶¬¬A (x , k))
  cbvᴿ (r⊗⇒ f)    x      k  = k (λ {(y , z) → cbvᴿ f (y , x) z})
  cbvᴿ (r⇐⊗ f)   (x , y) k  = cbvᴿ f x (A⟶¬¬A (k , y))
  cbvᴿ (r⊗⇐ f)    x      k  = k (λ {(y , z) → cbvᴿ f (x , z) y})
  cbvᴿ (m⊕  f g)  k      k′ = k′ (λ {(x , y) → k (cbvᴸ f x , cbvᴸ g y)})
  cbvᴿ (m⇛  f g) (x , y) k  = ¬¬A×¬¬B⟶¬¬[A×B] (A⟶¬¬A (cbvᴸ f x) , cbvᴿ g y) k
  cbvᴿ (m⇚  f g) (x , y) k  = ¬¬A×¬¬B⟶¬¬[A×B] (cbvᴿ f x , A⟶¬¬A (cbvᴸ g y)) k
  cbvᴿ (r⇛⊕ f)    x      k  = k (λ {(y , z) → cbvᴿ f (y , x) z})
  cbvᴿ (r⊕⇛ f)   (x , y) k  = cbvᴿ f y (A⟶¬¬A (x , k))
  cbvᴿ (r⊕⇚ f)   (x , y) k  = cbvᴿ f x (A⟶¬¬A (k , y))
  cbvᴿ (r⇚⊕ f)    x      k  = k (λ {(y , z) → cbvᴿ f (x , z) y})
  cbvᴿ (d⇛⇐ f)   (x , y) k  = k (λ {(z , w) → cbvᴿ f (y , w) (A⟶¬¬A (x , z))})
  cbvᴿ (d⇛⇒ f)   (x , y) k  = k (λ {(z , w) → cbvᴿ f (z , y) (A⟶¬¬A (x , w))})
  cbvᴿ (d⇚⇒ f)   (x , y) k  = k (λ {(z , w) → cbvᴿ f (z , x) (A⟶¬¬A (w , y))})
  cbvᴿ (d⇚⇐ f)   (x , y) k  = k (λ {(z , w) → cbvᴿ f (x , w) (A⟶¬¬A (z , y))})


mutual
  cbnᴸ : ∀ {A B} → LG A ⊢ B → (¬ ⌊ A ⌋ → ¬ ⌊ B ⌋)
  cbnᴸ f = cbvᴸ (f ∞ᵗ)

  cbnᴿ : ∀ {A B} → LG A ⊢ B → (⌊ B ⌋ → ¬ ¬ ⌊ A ⌋)
  cbnᴿ f = cbvᴿ (f ∞ᵗ)


⌈_⌉ᴶ : Judgement → Set ℓ
⌈ A ⊢ B ⌉ᴶ = ⌈ A ⌉ → ¬ ¬ ⌈ B ⌉


⌊_⌋ᴶ : Judgement → Set ℓ
⌊ A ⊢ B ⌋ᴶ = ¬ ⌊ A ⌋ → ¬ ⌊ B ⌋


CBV : Translation Type (Set ℓ) LG_ id
CBV = record
  { ⟦_⟧ᵀ = ⌈_⌉
  ; ⟦_⟧ᴶ = ⌈_⌉ᴶ
  ; [_]  = λ { {_ ⊢ _} f → cbvᴿ f}
  }


CBN : Translation Type (Set ℓ) LG_ id
CBN = record
  { ⟦_⟧ᵀ = ⌊_⌋
  ; ⟦_⟧ᴶ = ⌊_⌋ᴶ
  ; [_]  = λ { {_ ⊢ _} f → cbnᴸ f}
  }
