open import Level            renaming (suc to lsuc)
open import Function         using (_∘_)
open import Data.Empty       using (⊥)
open import Data.Fin         using (Fin; suc; zero)
open import Data.List        using (List; map; length; _++_) renaming ([] to ·; _∷_ to _,_)
open import Data.Product     using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry′)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as P 


module AHS.Type {ℓ₁} (Univ : Set ℓ₁) where

  infix  3 _⊢_ _⊢[_]_
  infixl 5 _‼_
  infixr 7 _⇒_
  infixl 9 _-_

  data Type : Set ℓ₁ where
    el  : Univ → Type
    _⇒_ : Type → Type → Type
    _-_ : Type → Type → Type
    _⊗_ : Type → Type → Type

  data Judgement : Set ℓ₁ where
    _⊢_    : List Type →        List Type → Judgement
    _⊢[_]_ : List Type → Type → List Type → Judgement


  _‼_ : ∀ {a} {A : Set a} (xs : List A) (i : Fin (length xs)) → A
  (    ·) ‼ ()
  (x , Γ) ‼ zero  = x
  (_ , Γ) ‼ suc i = Γ ‼ i

  split_at_ : (Γ : List Type) (α : Fin (length Γ)) → Σ[ Γ₁ ∈ _ ] Σ[ A ∈ _ ] Σ[ Γ₂ ∈ _ ] Γ ≡ Γ₁ ++ A , Γ₂ × Γ ‼ α ≡ A
  split     · at ()
  split A , Γ at zero  = (·  , (A , (Γ  , (refl , refl))))
  split A , Γ at suc α with (split Γ at α)
  split A , Γ at suc α | Γ₁ , (B , (Γ₂ , (p , q))) rewrite p | q = (A , Γ₁) , (B , (Γ₂ , (refl , refl )))


module Environment {ℓ₂} where

  data Env : List (Set ℓ₂) → Set (lsuc ℓ₂) where
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


  private
    lemma-⇒ : ∀ {a b} {A : Set a} {B : Set b} (k : ¬ ¬ (A → B)) → (¬ B → ¬ A)
    lemma-⇒ ¬¬[A→B] ¬B A = ¬¬[A→B] (λ A→B → ¬B (A→B A))

    lemma-⊗ : ∀ {a b} {A : Set a} {B : Set b} (k : ¬ ¬ (A × B)) → (¬ ¬ A × ¬ ¬ B)
    lemma-⊗ ¬¬[A×B] = (λ ¬A → ¬¬[A×B] (λ A×B → ¬A (proj₁ A×B)))
                    , (λ ¬B → ¬¬[A×B] (λ A×B → ¬B (proj₂ A×B)))


  infix 1 λΠ_

  ⟦_⟧ᵀ : Type → Set ℓ₂
  ⟦ el A  ⟧ᵀ =   ⟦ A ⟧ᵁ
  ⟦ A ⇒ B ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ → ¬ ⟦ A ⟧ᵀ
  ⟦ A - B ⟧ᵀ =      ¬ ⟦ B ⟧ᵀ ×   ⟦ A ⟧ᵀ
  ⟦ A ⊗ B ⟧ᵀ = ¬ ¬ (  ⟦ A ⟧ᵀ ×   ⟦ B ⟧ᵀ)

  ⟦_⟧⁺ : List Type → List (Set ℓ₂) 
  ⟦_⟧⁺ = map ⟦_⟧ᵀ

  ⟦_⟧⁻ : List Type → List (Set ℓ₂)
  ⟦_⟧⁻ = map (¬_ ∘ ⟦_⟧ᵀ)

  λΠ_ : Judgement → Set (lsuc ℓ₂)
  λΠ Γ ⊢      Δ = Env ⟦ Γ ⟧⁺ → Env ⟦     Δ ⟧⁻ → ⊥
  λΠ Γ ⊢[ A ] Δ = Env ⟦ Γ ⟧⁺ → Env ⟦ A , Δ ⟧⁻ → ⊥

