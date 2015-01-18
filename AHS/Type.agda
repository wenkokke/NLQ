open import Level                                      using (suc)
open import Function                                   using (_∘_)
open import Data.Empty                                 using (⊥)
open import Data.List                                  using (List; map; _++_) renaming ([] to ·; _∷_ to _,_)
open import Data.Product                               using (_×_; _,_; uncurry′)
open import Relation.Nullary                           using (¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module AHS.Type {ℓ₁} (Univ : Set ℓ₁) where

  infix  3 _⊢_ _⊢[_]_
  infixr 7 _⇾_
  infixl 9 _-_

  data Type : Set ℓ₁ where
    el  : Univ → Type
    _⇾_ : Type → Type → Type
    _-_ : Type → Type → Type

  setoid = P.setoid Type

  data Judgement : Set ℓ₁ where
    _⊢_    : List Type →        List Type → Judgement
    _⊢[_]_ : List Type → Type → List Type → Judgement


module Environment {ℓ₂} where

  data Env : List (Set ℓ₂) → Set (suc ℓ₂) where
    ·   : Env ·
    _,_ : {A : Set ℓ₂} {Γ : List (Set ℓ₂)} → A → Env Γ → Env (A , Γ)

  private
    module AbstractOverF {f : Type → Set ℓ₂} where
  
      split : ∀ {Γ₁ Γ₂} → Env (map f (Γ₁ ++ Γ₂)) → Env (map f Γ₁) × Env (map f Γ₂)
      split {Γ₁ = ·}      {Γ₂ = Γ₂}      e  =      ·   , e
      split {Γ₁ = _ , Γ₁} {Γ₂ = Γ₂} (x , e) with split {Γ₁ = Γ₁} {Γ₂ = Γ₂} e
      split {Γ₁ = _ , Γ₁} {Γ₂ = Γ₂} (x , e) | (e₁ , e₂) = (x , e₁) , e₂


      split_into_ : ∀ {ℓ₃} {R : Set ℓ₃} {Γ₁ Γ₂}
                    → Env (map f (Γ₁ ++ Γ₂)) → (Env (map f Γ₁) → Env (map f Γ₂) → R) → R
      split_into_ e f = uncurry′ f (split e)


      exchange : ∀ Γ₁ Γ₂ Γ₃ Γ₄
               → Env (map f ((Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄)))
               → Env (map f ((Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄)))
      exchange (_ , Γ₁) Γ₂      Γ₃  Γ₄ (x , e) = x , exchange Γ₁ Γ₂ Γ₃ Γ₄ e
      exchange      ·   Γ₂      ·   Γ₄      e  = e
      exchange      ·   Γ₂ (_ , Γ₃) Γ₄ (x , e) = insert Γ₂ (Γ₃ ++ Γ₄) x (exchange · Γ₂ Γ₃ Γ₄ e)
        where
          insert : ∀ {A} Γ₁ Γ₂ → f A → Env (map f (Γ₁ ++ Γ₂)) → Env (map f (Γ₁ ++ (A , Γ₂)))
          insert      ·   Γ₂ x      e  = x , e
          insert (_ , Γ₁) Γ₂ x (y , e) = y , insert Γ₁ Γ₂ x e

  open AbstractOverF public


module ToAgda {ℓ₂} (⟦_⟧ᵁ : Univ → Set ℓ₂) where

  open Environment public

  infix 1 λΠ_
  
  ⟦_⟧ᵀ : Type → Set ℓ₂
  ⟦ el A  ⟧ᵀ = ⟦ A ⟧ᵁ
  ⟦ A ⇾ B ⟧ᵀ = ¬ ⟦ B ⟧ᵀ → ¬ ⟦ A ⟧ᵀ
  ⟦ A - B ⟧ᵀ = ¬ ⟦ B ⟧ᵀ ×   ⟦ A ⟧ᵀ

  ⟦_⟧⁺ : List Type → List (Set ℓ₂) 
  ⟦_⟧⁺ = map ⟦_⟧ᵀ

  ⟦_⟧⁻ : List Type → List (Set ℓ₂)
  ⟦_⟧⁻ = map (¬_ ∘ ⟦_⟧ᵀ)

  λΠ_ : Judgement → Set (suc ℓ₂)
  λΠ Γ ⊢      Δ = Env ⟦ Γ ⟧⁺ → Env ⟦     Δ ⟧⁻ → ⊥
  λΠ Γ ⊢[ A ] Δ = Env ⟦ Γ ⟧⁺ → Env ⟦ A , Δ ⟧⁻ → ⊥
