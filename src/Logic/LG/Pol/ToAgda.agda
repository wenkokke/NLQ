------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function                              using (id; _∘_; flip)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Product                          using (∃; _×_; _,_; proj₁)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Logic.Polarity


module Logic.LG.Pol.ToAgda
  {a ℓ} (Atom : Set a)
        (⟦_⟧ᴬ : Atom → Set ℓ) (R : Set ℓ)
        (Polarityᴬ? : Atom → Polarity) where


open import Logic.Translation
open import Logic.LG.Type.Polarised      Atom Polarityᴬ?
open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Sequent           Atom
open import Logic.LG.Pol.Base            Atom Polarityᴬ?


mutual
  ⟦_⟧⁺ : Type → Set ℓ
  ⟦ el  A ⟧⁺ with Polarityᴬ? A
  ⟦ el  A ⟧⁺ | + =  ⟦ A ⟧ᴬ
  ⟦ el  A ⟧⁺ | - = (⟦ A ⟧ᴬ → R) → R
  ⟦ □   A ⟧⁺     =  ⟦ A ⟧⁻ → R
  ⟦ ◇   A ⟧⁺     =  ⟦ A ⟧⁺
  ⟦ ₀   A ⟧⁺     =  ⟦ A ⟧⁺ → R
  ⟦ A   ⁰ ⟧⁺     =  ⟦ A ⟧⁺ → R
  ⟦ ₁   A ⟧⁺     =  ⟦ A ⟧⁻
  ⟦ A   ¹ ⟧⁺     =  ⟦ A ⟧⁻
  ⟦ A ⊗ B ⟧⁺     =  ⟦ A ⟧⁺ × ⟦ B ⟧⁺
  ⟦ A ⇚ B ⟧⁺     =  ⟦ A ⟧⁺ × ⟦ B ⟧⁻
  ⟦ A ⇛ B ⟧⁺     =  ⟦ A ⟧⁻ × ⟦ B ⟧⁺
  ⟦ A ⊕ B ⟧⁺     = (⟦ A ⟧⁻ × ⟦ B ⟧⁻) → R
  ⟦ A ⇒ B ⟧⁺     = (⟦ A ⟧⁺ × ⟦ B ⟧⁻) → R
  ⟦ A ⇐ B ⟧⁺     = (⟦ A ⟧⁻ × ⟦ B ⟧⁺) → R

  ⟦_⟧⁻ : Type → Set ℓ
  ⟦ el  A ⟧⁻     =  ⟦ A ⟧ᴬ → R
  ⟦ □   A ⟧⁻     =  ⟦ A ⟧⁻
  ⟦ ◇   A ⟧⁻     =  ⟦ A ⟧⁺ → R
  ⟦ ₀   A ⟧⁻     =  ⟦ A ⟧⁺
  ⟦ A   ⁰ ⟧⁻     =  ⟦ A ⟧⁺
  ⟦ ₁   A ⟧⁻     =  ⟦ A ⟧⁻ → R
  ⟦ A   ¹ ⟧⁻     =  ⟦ A ⟧⁻ → R
  ⟦ A ⊗ B ⟧⁻     = (⟦ A ⟧⁺ × ⟦ B ⟧⁺) → R
  ⟦ A ⇚ B ⟧⁻     = (⟦ A ⟧⁺ × ⟦ B ⟧⁻) → R
  ⟦ A ⇛ B ⟧⁻     = (⟦ A ⟧⁻ × ⟦ B ⟧⁺) → R
  ⟦ A ⊕ B ⟧⁻     =  ⟦ A ⟧⁻ × ⟦ B ⟧⁻
  ⟦ A ⇒ B ⟧⁻     =  ⟦ A ⟧⁺ × ⟦ B ⟧⁻
  ⟦ A ⇐ B ⟧⁻     =  ⟦ A ⟧⁻ × ⟦ B ⟧⁺


app₁ : ∀ {A} {{n : True (Negative?  A)}}  →  ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
app₁ {{n}} = app (toWitness n)
  where
    app : ∀ {A} (n : Negative A) → ⟦ A ⟧⁻ → (⟦ A ⟧⁺ → R)
    app (el  A) x f with Polarityᴬ? A
    app (el  A {{()}}) x f | +
    app (el  A       ) x f | - = f x
    app (□   A) x f = f x
    app (₀   A) x f = f x
    app (A   ⁰) x f = f x
    app (A ⊕ B) x f = f x
    app (A ⇒ B) x f = f x
    app (A ⇐ B) x f = f x

app₂ : ∀ {B} {{p : True (Positive?  B)}}  →  ⟦ B ⟧⁺ → ⟦ B ⟧⁻ → R
app₂ {{p}} = app (toWitness p)
  where
    app : ∀ {A} (p : Positive A) → ⟦ A ⟧⁺ → (⟦ A ⟧⁻ → R)
    app (el  A) x f with Polarityᴬ? A
    app (el  A       ) x f | + = f x
    app (el  A {{()}}) _ _ | -
    app (◇   A) x f = f x
    app (₁   A) x f = f x
    app (A   ¹) x f = f x
    app (A ⊗ B) x f = f x
    app (A ⇚ B) x f = f x
    app (A ⇛ B) x f = f x

app₃ : ∀ {A} {{p : True (Positive?  A)}}  → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
app₃ {{p}} = app (toWitness p)
  where
    app : ∀ {A} (p : Positive A) → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
    app (el  A) f x with Polarityᴬ? A
    app (el  A       ) f x | + = f x
    app (el  A {{()}}) f x | -
    app (◇   A) f x = f x
    app (₁   A) f x = f x
    app (A   ¹) f x = f x
    app (A ⊗ B) f x = f x
    app (A ⇚ B) f x = f x
    app (A ⇛ B) f x = f x

app₄ : ∀ {B} {{n : True (Negative?  B)}}  → (⟦ B ⟧⁻ → R) → ⟦ B ⟧⁺
app₄ {{n}} = app (toWitness n)
  where
    app : ∀ {A} (n : Negative A) → (⟦ A ⟧⁻ → R) → ⟦ A ⟧⁺
    app (el  A) k with Polarityᴬ? A
    app (el  A {{()}}) k | +
    app (el  A       ) k | - = k
    app (□   A) f x = f x
    app (₀   A) f x = f x
    app (A   ⁰) f x = f x
    app (A ⊕ B) f x = f x
    app (A ⇒ B) f x = f x
    app (A ⇐ B) f x = f x


⟦_⟧ˢ : ∀ {p} → Structure p → Set ℓ
⟦ ·_· { + } A ⟧ˢ = ⟦ A ⟧⁺
⟦ ·_· { - } A ⟧ˢ = ⟦ A ⟧⁻
⟦     [ X ]   ⟧ˢ = ⟦ X ⟧ˢ
⟦     ⟨ X ⟩   ⟧ˢ = ⟦ X ⟧ˢ
⟦     ₀   X   ⟧ˢ = ⟦ X ⟧ˢ
⟦     X   ⁰   ⟧ˢ = ⟦ X ⟧ˢ
⟦     ₁   X   ⟧ˢ = ⟦ X ⟧ˢ
⟦     X   ¹   ⟧ˢ = ⟦ X ⟧ˢ
⟦     X ⊗ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⇚ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⇛ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⊕ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⇒ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⇐ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ


⟦_⟧ʲ : Sequent → Set ℓ
⟦   X  ⊢  Y   ⟧ʲ = ⟦ X ⟧ˢ → ⟦ Y ⟧ˢ → R
⟦ [ A ]⊢  Y   ⟧ʲ = ⟦ Y ⟧ˢ → ⟦ A ⟧⁻
⟦   X  ⊢[ B ] ⟧ʲ = ⟦ X ⟧ˢ → ⟦ B ⟧⁺


⟦_⟧ : ∀ {J} → fLG J → ⟦ J ⟧ʲ
⟦ ax⁺      ⟧ = λ x → x
⟦ ax⁻      ⟧ = λ x → x
⟦ ↼{A} f   ⟧ = λ y x → app₁ {A} (⟦ f ⟧ x) y
⟦ ⇀{A} f   ⟧ = λ x y → app₂ {A} (⟦ f ⟧ x) y
⟦ ↽{A} f   ⟧ = λ y   → app₃ {A} (λ x → ⟦ f ⟧ x y)
⟦ ⇁{A} f   ⟧ = λ x   → app₄ {A} (λ y → ⟦ f ⟧ x y)
⟦ ◇ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ◇ᴿ   f   ⟧ = ⟦ f ⟧
⟦ □ᴸ   f   ⟧ = ⟦ f ⟧
⟦ □ᴿ   f   ⟧ = ⟦ f ⟧
⟦ r□◇  f   ⟧ = ⟦ f ⟧
⟦ r◇□  f   ⟧ = ⟦ f ⟧
⟦ ₀ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ₀ᴿ   f   ⟧ = ⟦ f ⟧
⟦ ⁰ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ⁰ᴿ   f   ⟧ = ⟦ f ⟧
⟦ ₁ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ₁ᴿ   f   ⟧ = ⟦ f ⟧
⟦ ¹ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ¹ᴿ   f   ⟧ = ⟦ f ⟧
⟦ r⁰₀  f   ⟧ = flip ⟦ f ⟧
⟦ r₀⁰  f   ⟧ = flip ⟦ f ⟧
⟦ r¹₁  f   ⟧ = flip ⟦ f ⟧
⟦ r₁¹  f   ⟧ = flip ⟦ f ⟧
⟦ ⊗ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ⊗ᴿ   f g ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
⟦ ⇒ᴸ   f g ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
⟦ ⇒ᴿ   f   ⟧ = ⟦ f ⟧
⟦ ⇐ᴸ   f g ⟧ = λ{(x , y) → ⟦ g ⟧ x , ⟦ f ⟧ y}
⟦ ⇐ᴿ   f   ⟧ = ⟦ f ⟧
⟦ r⇒⊗  f   ⟧ = λ{(x , y) z → ⟦ f ⟧ y (x , z)}
⟦ r⊗⇒  f   ⟧ = λ{y (x , z) → ⟦ f ⟧ (x , y) z}
⟦ r⇐⊗  f   ⟧ = λ{(x , y) z → ⟦ f ⟧ x (z , y)}
⟦ r⊗⇐  f   ⟧ = λ{x (z , y) → ⟦ f ⟧ (x , y) z}
⟦ ⊕ᴸ   f g ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
⟦ ⊕ᴿ   f   ⟧ = ⟦ f ⟧
⟦ ⇚ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ⇚ᴿ   f g ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
⟦ ⇛ᴸ   f   ⟧ = ⟦ f ⟧
⟦ ⇛ᴿ   f g ⟧ = λ{(x , y) → ⟦ g ⟧ x , ⟦ f ⟧ y}
⟦ r⇚⊕  f   ⟧ = λ {z (y , x) → ⟦ f ⟧ (z , x) y}
⟦ r⊕⇚  f   ⟧ = λ {(z , x) y → ⟦ f ⟧ z (y , x)}
⟦ r⇛⊕  f   ⟧ = λ {z (y , x) → ⟦ f ⟧ (y , z) x}
⟦ r⊕⇛  f   ⟧ = λ {(y , z) x → ⟦ f ⟧ z (y , x)}
⟦ d⇛⇐  f   ⟧ = λ {(z , x) (w , y) → ⟦ f ⟧ (x , y) (z , w)}
⟦ d⇛⇒  f   ⟧ = λ {(z , y) (x , w) → ⟦ f ⟧ (x , y) (z , w)}
⟦ d⇚⇒  f   ⟧ = λ {(y , w) (x , z) → ⟦ f ⟧ (x , y) (z , w)}
⟦ d⇚⇐  f   ⟧ = λ {(x , w) (z , y) → ⟦ f ⟧ (x , y) (z , w)}


fLG→λΠ : Translation Type (Set ℓ) fLG_ id
fLG→λΠ = record { ⟦_⟧ᵗ = ⟦_⟧⁺ ; ⟦_⟧ʲ = ⟦_⟧ʲ ; [_]  = ⟦_⟧ }
