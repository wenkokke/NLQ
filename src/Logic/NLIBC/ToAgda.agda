------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level        using (Lift; lift)
open import Function     using (id)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; map; proj₁; proj₂; curry; uncurry)


module Logic.NLIBC.ToAgda {ℓ ℓ₂} (Atom : Set ℓ) (⟦_⟧ᴬ : Atom → Set ℓ₂) where


open import Logic.NLIBC Atom


⟦_⟧ᵗ : Type → Set ℓ₂
⟦ el  p ⟧ᵗ = ⟦ p ⟧ᴬ
⟦ p ⇒ q ⟧ᵗ = ⟦ p ⟧ᵗ → ⟦ q ⟧ᵗ
⟦ q ⇐ p ⟧ᵗ = ⟦ p ⟧ᵗ → ⟦ q ⟧ᵗ
⟦ p ⇨ q ⟧ᵗ = ⟦ p ⟧ᵗ → ⟦ q ⟧ᵗ
⟦ q ⇦ p ⟧ᵗ = ⟦ p ⟧ᵗ → ⟦ q ⟧ᵗ


⟦_⟧ˢ : Structure → Set ℓ₂
⟦ · p · ⟧ˢ = ⟦ p ⟧ᵗ
⟦ Γ ∙ Δ ⟧ˢ = ⟦ Γ ⟧ˢ × ⟦ Δ ⟧ˢ
⟦ Γ ∘ Δ ⟧ˢ = ⟦ Γ ⟧ˢ × ⟦ Δ ⟧ˢ
⟦ I     ⟧ˢ = Lift ⊤
⟦ B     ⟧ˢ = Lift ⊤
⟦ C     ⟧ˢ = Lift ⊤


⟦_⟧ʲ : Judgement → Set ℓ₂
⟦ Γ ⊢ p ⟧ʲ = ⟦ Γ ⟧ˢ → ⟦ p ⟧ᵗ

private
  cut : ∀ (Γ : Context) {Δ Δ′} → (⟦ Δ ⟧ˢ → ⟦ Δ′ ⟧ˢ) → ⟦ Γ [ Δ ] ⟧ˢ → ⟦ Γ [ Δ′ ] ⟧ˢ
  cut []       f x = f x
  cut (_ ∙> Γ) f x = map id (cut Γ f) x
  cut (Γ <∙ _) f x = map (cut Γ f) id x
  cut (_ ∘> Γ) f x = map id (cut Γ f) x
  cut (Γ <∘ _) f x = map (cut Γ f) id x

⟦_⟧ : ∀ {J} → NL J → ⟦ J ⟧ʲ
⟦ ax                   ⟧ x   = x

⟦ ⇒ᴸ Σ             f g ⟧ x   = ⟦ g ⟧ (cut Σ (λ p → proj₂ p (⟦ f ⟧ (proj₁ p))) x)
⟦ ⇒ᴿ               f   ⟧ x y = ⟦ f ⟧ (y , x)
⟦ ⇐ᴸ Σ             f g ⟧ x   = ⟦ g ⟧ (cut Σ (λ p → proj₁ p (⟦ f ⟧ (proj₂ p))) x)
⟦ ⇐ᴿ               f   ⟧ x y = ⟦ f ⟧ (x , y)

⟦ ⇨ᴸ Σ             f g ⟧ x   = ⟦ g ⟧ (cut Σ (λ p → proj₂ p (⟦ f ⟧ (proj₁ p))) x)
⟦ ⇨ᴿ               f   ⟧ x y = ⟦ f ⟧ (y , x)
⟦ ⇦ᴸ Σ             f g ⟧ x   = ⟦ g ⟧ (cut Σ (λ p → proj₁ p (⟦ f ⟧ (proj₂ p))) x)
⟦ ⇦ᴿ               f   ⟧ x y = ⟦ f ⟧ (x , y)

⟦ Iᵢ Σ {p}         f   ⟧ x   = ⟦ f ⟧ (cut Σ Iᵢ′ x)
  where
    Iᵢ′ : ⟦ p ⟧ˢ → ⟦ p ⟧ˢ × (Lift {ℓ = ℓ₂} ⊤)
    Iᵢ′ p = (p , lift tt)
⟦ Iₑ Σ {p}         f   ⟧ x   = ⟦ f ⟧ (cut Σ Iₑ′ x)
  where
    Iₑ′ : ⟦ p ⟧ˢ × (Lift {ℓ = ℓ₂} ⊤) → ⟦ p ⟧ˢ
    Iₑ′ (p , _) = p
⟦ Bᵢ Σ {p} {q} {r} f   ⟧ x   = ⟦ f ⟧ (cut Σ Bᵢ′ x)
  where
    Bᵢ′ : ⟦ p ⟧ˢ × ⟦ q ⟧ˢ × ⟦ r ⟧ˢ → ⟦ q ⟧ˢ × (Lift {ℓ = ℓ₂} ⊤ × ⟦ p ⟧ˢ) × ⟦ r ⟧ˢ
    Bᵢ′ (p , q , r) = q , (lift tt , p) , r
⟦ Bₑ Σ {p} {q} {r} f   ⟧ x   = ⟦ f ⟧ (cut Σ Bₑ′ x)
  where
    Bₑ′ : ⟦ q ⟧ˢ × (Lift {ℓ = ℓ₂} ⊤ × ⟦ p ⟧ˢ) × ⟦ r ⟧ˢ → ⟦ p ⟧ˢ × ⟦ q ⟧ˢ × ⟦ r ⟧ˢ
    Bₑ′ (q , (_ , p) , r) = (p , q , r)
⟦ Cᵢ Σ {p} {q} {r} f   ⟧ x   = ⟦ f ⟧ (cut Σ Cᵢ′ x)
  where
    Cᵢ′ : (⟦ p ⟧ˢ × ⟦ q ⟧ˢ) × ⟦ r ⟧ˢ → ⟦ p ⟧ˢ × (Lift {ℓ = ℓ₂} ⊤ × ⟦ q ⟧ˢ) × ⟦ r ⟧ˢ
    Cᵢ′ ((p , q) , r) = p , (lift tt , q) , r
⟦ Cₑ Σ {p} {q} {r} f   ⟧ x   = ⟦ f ⟧ (cut Σ Cₑ′ x)
  where
    Cₑ′ : ⟦ p ⟧ˢ × (Lift {ℓ = ℓ₂} ⊤ × ⟦ q ⟧ˢ) × ⟦ r ⟧ˢ → (⟦ p ⟧ˢ × ⟦ q ⟧ˢ) × ⟦ r ⟧ˢ
    Cₑ′ (p , (_ , q) , r) = ((p , q) , r)
