------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level        using (suc)
open import Function     using (_∘_) renaming (id to λΠ_)
open import Data.List    using (List; _∷_; map)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Classical.Unrestricted.LambdaCMinus.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) (R : Set ℓ₂) where


open import Logic.Translation
open import Logic.Classical.Unrestricted.LambdaCMinus.Type      Univ renaming (_⇚_ to _-_)
open import Logic.Classical.Unrestricted.LambdaCMinus.Judgement Univ
open import Logic.Classical.Unrestricted.LambdaCMinus.Base      Univ
open import Logic.Intuitionistic.Unrestricted.Agda.Environment


infixr 5 ¬_


private
  ¬_  : Set ℓ₂ → Set ℓ₂
  ¬ A = A → R


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
  ⟦ A - B ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ ×   ⟦ A ⟧ᵀ
  ⟦ A ⊗ B ⟧ᵀ = ¬ ¬ (  ⟦ A ⟧ᵀ ×   ⟦ B ⟧ᵀ)
  ⟦ A ⊕ B ⟧ᵀ = ¬   (¬ ⟦ A ⟧ᵀ × ¬ ⟦ B ⟧ᵀ)


  ⟦_⟧⁺ : List Type → List (Set ℓ₂)
  ⟦_⟧⁺ = map ⟦_⟧ᵀ


  ⟦_⟧⁻ : List Type → List (Set ℓ₂)
  ⟦_⟧⁻ = map (¬_ ∘ ⟦_⟧ᵀ)


  ⟦_⟧ᴶ : Judgement → Set (suc ℓ₂)
  ⟦ Γ ⊢      Δ ⟧ᴶ = Env ⟦ Γ ⟧⁺ → Env ⟦     Δ ⟧⁻ → R
  ⟦ Γ ⊢[ A ] Δ ⟧ᴶ = Env ⟦ Γ ⟧⁺ → Env ⟦ A ∷ Δ ⟧⁻ → R


  [_] : ∀ {J} → λC⁻ J → λΠ ⟦ J ⟧ᴶ
  [ ax                   ] (x ∷ []) (k ∷ _) = k x
  [ ⇒ᵢ               f   ]      e  (k ∷ r) = k (λ k x → [ f ] (x ∷ e) (k ∷ r))
  [ ⇒ₑ               f g ]      e  (k ∷ r) = split e into λ e₁ e₂ → [ f ] e₁ ((λ x → [ g ] e₂ (x k ∷ r)) ∷ r)
  [ raa              f   ]      e  (k ∷ r) = [ f ] e (     k ∷ r )
  [ ⇒ₑᵏ              α f ]      e       r  = [ f ] e (lookup r α ∷ r)
  [ -ᵢ               f g ]      e  (k ∷ r) = split e into λ e₁ e₂ → [ f ] e₁ ((λ x → k ((λ y → [ g ] (y ∷ e₂) r) , x)) ∷ r)
  [ -ₑ               f g ]      e  (k ∷ r) = split e into λ e₁ e₂ → [ f ] e₁ ((λ {(x , y) → [ g ] (y ∷ e₂) (k ∷ (x ∷ r))}) ∷ r)
  [ ⊗ᵢ               f g ]      e  (k ∷ r) = split e into λ e₁ e₂ → [ f ] e₁ ((λ x → [ g ] e₂ ((λ y → k (λ l → l (x , y))) ∷ r)) ∷ r)
  [ ⊗ₑ               f g ]      e  (k ∷ r) = split e into λ e₁ e₂ → [ f ] e₁ ((λ l → l (λ {(x , y) → [ g ] (x ∷ (y ∷ e₂)) ((λ z → k z) ∷ r)})) ∷ r)
  [ eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ f   ]      e  (k ∷ r) = [ f ] (exchange Γ₁ Γ₃ Γ₂ Γ₄ e) (k ∷ r)
  [ cᴸ₁              f   ] (x ∷ e) (k ∷ r) = [ f ] (x ∷ (x ∷ e)) (k ∷ r)
  [ wᴸ₁              f   ] (x ∷ e) (k ∷ r) = [ f ]           e   (k ∷ r)


Un→Agda : Translation Type (Set ℓ₂) λC⁻_ λΠ_
Un→Agda = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
