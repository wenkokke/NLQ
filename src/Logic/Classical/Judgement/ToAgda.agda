open import Level        using (suc)
open import Function     using (_∘_)
open import Data.List    using (List; map) renaming (_∷_ to _,_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Classical.Judgement.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) (R : Set ℓ₂) where


open import Logic.Type Univ
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open import Logic.Classical.Judgement Univ


¬_  : Set ℓ₂ → Set ℓ₂
¬ A = A → R


-- Lemma: justification for the types that are derived below.
private
  lemma-→ : ∀ {A B} (k : ¬ ¬ (A → B)) → (¬ B → ¬ A)
  lemma-→ ¬¬[A→B] ¬B A = ¬¬[A→B] (λ A→B → ¬B (A→B A))

  lemma-× : ∀ {A B} (k : ¬ ¬ (A × B)) → (¬ ¬ A × ¬ ¬ B)
  lemma-× ¬¬[A×B] = ((λ ¬A → ¬¬[A×B] (¬A ∘ proj₁)) , (λ ¬B → ¬¬[A×B] (¬B ∘ proj₂)))

  lemma-⊎ : ∀ {A B} (k : ¬ ¬ (A ⊎ B)) → (¬ (¬ A × ¬ B))
  lemma-⊎ ¬¬[A+B] (¬A , ¬B) = ¬¬[A+B] [ ¬A , ¬B ]


infix 1 λΠ_

⟦_⟧ : Type → Set ℓ₂
⟦ el A  ⟧ =        ⟦ A ⟧ᵁ
⟦ A ⇒ B ⟧ =      ¬ ⟦ B ⟧ → ¬ ⟦ A ⟧
⟦ A ⇚ B ⟧ =      ¬ ⟦ B ⟧ ×   ⟦ A ⟧
⟦ A ⊗ B ⟧ = ¬ ¬ (  ⟦ A ⟧ ×   ⟦ B ⟧)
⟦ B ⇐ A ⟧ =      ¬ ⟦ B ⟧ → ¬ ⟦ A ⟧
⟦ B ⇛ A ⟧ =      ¬ ⟦ B ⟧ ×   ⟦ A ⟧
⟦ A ⊕ B ⟧ = ¬   (¬ ⟦ A ⟧ × ¬ ⟦ B ⟧)

⟦_⟧⁺ : List Type → List (Set ℓ₂) 
⟦_⟧⁺ = map ⟦_⟧

⟦_⟧⁻ : List Type → List (Set ℓ₂)
⟦_⟧⁻ = map (¬_ ∘ ⟦_⟧)

λΠ_ : Judgement → Set (suc ℓ₂)
λΠ Γ ⊢      Δ = Env ⟦ Γ ⟧⁺ → Env ⟦     Δ ⟧⁻ → R
λΠ Γ ⊢[ A ] Δ = Env ⟦ Γ ⟧⁺ → Env ⟦ A , Δ ⟧⁻ → R
