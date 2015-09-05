--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/Pol/ToAgda.agda
--------------------------------------------------------------------------------


open import Function                              using (id; _∘_; flip)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Product                          using (∃; _×_; _,_; proj₁)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Logic.Polarity


module Logic.NL.Pol.ToAgda
  {a ℓ} (Atom : Set a)
        (⟦_⟧ᴬ : Atom → Set ℓ) (R : Set ℓ)
        (Polarityᴬ? : Atom → Polarity) where


open import Logic.Translation
open import Logic.NL.Type.Polarised      Atom Polarityᴬ?
open import Logic.NL.Type                Atom
open import Logic.NL.Structure.Polarised Atom
open import Logic.NL.Sequent           Atom
open import Logic.NL.Pol.Base            Atom Polarityᴬ?


mutual
  ⟦_⟧⁺ : Type → Set ℓ
  ⟦ el  A ⟧⁺ with Polarityᴬ? A
  ⟦ el  A ⟧⁺ | + =  ⟦ A ⟧ᴬ
  ⟦ el  A ⟧⁺ | - = (⟦ A ⟧ᴬ → R) → R
  ⟦ A ⊗ B ⟧⁺     =  ⟦ A ⟧⁺ × ⟦ B ⟧⁺
  ⟦ A ⇒ B ⟧⁺     = (⟦ A ⟧⁺ × ⟦ B ⟧⁻) → R
  ⟦ A ⇐ B ⟧⁺     = (⟦ A ⟧⁻ × ⟦ B ⟧⁺) → R

  ⟦_⟧⁻ : Type → Set ℓ
  ⟦ el  A ⟧⁻     =  ⟦ A ⟧ᴬ → R
  ⟦ A ⊗ B ⟧⁻     = (⟦ A ⟧⁺ × ⟦ B ⟧⁺) → R
  ⟦ A ⇒ B ⟧⁻     =  ⟦ A ⟧⁺ × ⟦ B ⟧⁻
  ⟦ A ⇐ B ⟧⁻     =  ⟦ A ⟧⁻ × ⟦ B ⟧⁺


app₁ : ∀ {A} {{n : True (Negative?  A)}}  →  ⟦ A ⟧⁻ → ⟦ A ⟧⁺ → R
app₁ {{n}} = app (toWitness n)
  where
    app : ∀ {A} (n : Negative A) → ⟦ A ⟧⁻ → (⟦ A ⟧⁺ → R)
    app (el  A) x f with Polarityᴬ? A
    app (el  A {{()}}) x f | +
    app (el  A       ) x f | - = f x
    app (A ⇒ B) x f = f x
    app (A ⇐ B) x f = f x

app₂ : ∀ {B} {{p : True (Positive?  B)}}  →  ⟦ B ⟧⁺ → ⟦ B ⟧⁻ → R
app₂ {{p}} = app (toWitness p)
  where
    app : ∀ {A} (p : Positive A) → ⟦ A ⟧⁺ → (⟦ A ⟧⁻ → R)
    app (el  A) x f with Polarityᴬ? A
    app (el  A       ) x f | + = f x
    app (el  A {{()}}) _ _ | -
    app (A ⊗ B) x f = f x
app₃ : ∀ {A} {{p : True (Positive?  A)}}  → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
app₃ {{p}} = app (toWitness p)
  where
    app : ∀ {A} (p : Positive A) → (⟦ A ⟧⁺ → R) → ⟦ A ⟧⁻
    app (el  A) f x with Polarityᴬ? A
    app (el  A       ) f x | + = f x
    app (el  A {{()}}) f x | -
    app (A ⊗ B) f x = f x
app₄ : ∀ {B} {{n : True (Negative?  B)}}  → (⟦ B ⟧⁻ → R) → ⟦ B ⟧⁺
app₄ {{n}} = app (toWitness n)
  where
    app : ∀ {A} (n : Negative A) → (⟦ A ⟧⁻ → R) → ⟦ A ⟧⁺
    app (el  A) k with Polarityᴬ? A
    app (el  A {{()}}) k | +
    app (el  A       ) k | - = k
    app (A ⇒ B) f x = f x
    app (A ⇐ B) f x = f x


⟦_⟧ˢ : ∀ {p} → Structure p → Set ℓ
⟦ ·_· { + } A ⟧ˢ = ⟦ A ⟧⁺
⟦ ·_· { - } A ⟧ˢ = ⟦ A ⟧⁻
⟦     X ⊗ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⇒ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ
⟦     X ⇐ Y   ⟧ˢ = ⟦ X ⟧ˢ × ⟦ Y ⟧ˢ


⟦_⟧ʲ : Sequent → Set ℓ
⟦   X  ⊢  Y   ⟧ʲ = ⟦ X ⟧ˢ → ⟦ Y ⟧ˢ → R
⟦ [ A ]⊢  Y   ⟧ʲ = ⟦ Y ⟧ˢ → ⟦ A ⟧⁻
⟦   X  ⊢[ B ] ⟧ʲ = ⟦ X ⟧ˢ → ⟦ B ⟧⁺


⟦_⟧ : ∀ {J} → fNL J → ⟦ J ⟧ʲ
⟦ ax⁺      ⟧ = λ x → x
⟦ ax⁻      ⟧ = λ x → x
⟦ ↼{A} f   ⟧ = λ y x → app₁ {A} (⟦ f ⟧ x) y
⟦ ⇀{A} f   ⟧ = λ x y → app₂ {A} (⟦ f ⟧ x) y
⟦ ↽{A} f   ⟧ = λ y   → app₃ {A} (λ x → ⟦ f ⟧ x y)
⟦ ⇁{A} f   ⟧ = λ x   → app₄ {A} (λ y → ⟦ f ⟧ x y)
⟦ ⊗L   f   ⟧ = ⟦ f ⟧
⟦ ⊗R   f g ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
⟦ ⇒L   f g ⟧ = λ{(x , y) → ⟦ f ⟧ x , ⟦ g ⟧ y}
⟦ ⇒R   f   ⟧ = ⟦ f ⟧
⟦ ⇐L   f g ⟧ = λ{(x , y) → ⟦ g ⟧ x , ⟦ f ⟧ y}
⟦ ⇐R   f   ⟧ = ⟦ f ⟧
⟦ r⇒⊗  f   ⟧ = λ{(x , y) z → ⟦ f ⟧ y (x , z)}
⟦ r⊗⇒  f   ⟧ = λ{y (x , z) → ⟦ f ⟧ (x , y) z}
⟦ r⇐⊗  f   ⟧ = λ{(x , y) z → ⟦ f ⟧ x (z , y)}
⟦ r⊗⇐  f   ⟧ = λ{x (z , y) → ⟦ f ⟧ (x , y) z}
fNL→λΠ : Translation Type (Set ℓ) fNL_ id
fNL→λΠ = record { ⟦_⟧ᵗ = ⟦_⟧⁺ ; ⟦_⟧ʲ = ⟦_⟧ʲ ; [_]  = ⟦_⟧ }
