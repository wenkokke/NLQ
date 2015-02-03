open import Level        using (suc)
open import Function     using (_∘_)
open import Data.List    using (List; map) renaming (_∷_ to _,_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Judgement.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) (R : Set ℓ₂) where


open import Logic.Type Univ
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open import Logic.Judgement (List Type) Type (List Type)


-- This entire module should probably live in Logic.Classical.Unrestricted.
-- LambdaCMinus, because it is specific to that logic.
module CPS where

  ¬_  : Set ℓ₂ → Set ℓ₂
  ¬ A = A → R
  
  private
    -- Lemma: justification for the types that are derived below.
    lemma-→ : ∀ {A B} (k : ¬ ¬ (A → B)) → (¬ B → ¬ A)
    lemma-→ ¬¬[A→B] ¬B A = ¬¬[A→B] (λ A→B → ¬B (A→B A))
  
    lemma-× : ∀ {A B} (k : ¬ ¬ (A × B)) → (¬ ¬ A × ¬ ¬ B)
    lemma-× ¬¬[A×B] = ((λ ¬A → ¬¬[A×B] (¬A ∘ proj₁)) , (λ ¬B → ¬¬[A×B] (¬B ∘ proj₂)))
  
    lemma-⊎ : ∀ {A B} (k : ¬ ¬ (A ⊎ B)) → (¬ (¬ A × ¬ B))
    lemma-⊎ ¬¬[A+B] (¬A , ¬B) = ¬¬[A+B] [ ¬A , ¬B ]
  
  
  -- Translation to Agda
  ⟦_⟧ᵀ : Type → Set ℓ₂
  ⟦ el A  ⟧ᵀ =        ⟦ A ⟧ᵁ
  ⟦ A ⇒ B ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ → ¬ ⟦ A ⟧ᵀ
  ⟦ B ⇐ A ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ → ¬ ⟦ A ⟧ᵀ
  ⟦ A ⇚ B ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ ×   ⟦ A ⟧ᵀ
  ⟦ B ⇛ A ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ ×   ⟦ A ⟧ᵀ
  ⟦ A ⊗ B ⟧ᵀ = ¬ ¬ (  ⟦ A ⟧ᵀ ×   ⟦ B ⟧ᵀ)
  ⟦ A ⊕ B ⟧ᵀ = ¬   (¬ ⟦ A ⟧ᵀ × ¬ ⟦ B ⟧ᵀ)
    
  ⟦_⟧⁺ : List Type → List (Set ℓ₂) 
  ⟦_⟧⁺ = map ⟦_⟧ᵀ
    
  ⟦_⟧⁻ : List Type → List (Set ℓ₂)
  ⟦_⟧⁻ = map (¬_ ∘ ⟦_⟧ᵀ)
    
  ⟦_⟧ᴶ : Judgement → Set (suc ℓ₂)
  ⟦ Γ ⊢      Δ ⟧ᴶ = Env ⟦ Γ ⟧⁺ → Env ⟦     Δ ⟧⁻ → R
  ⟦ Γ ⊢[ A ] Δ ⟧ᴶ = Env ⟦ Γ ⟧⁺ → Env ⟦ A , Δ ⟧⁻ → R
      
