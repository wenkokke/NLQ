------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level using (suc)
open import Data.Product using (_×_; _,_)
open import Logic.Reification


module Logic.Intuitionistic.Agda.Environment
  {ℓ₁ ℓ₂} (Type : Set ℓ₁) (Type→Set : Reify Type (Set ℓ₂))
  where


open import Logic.Intuitionistic.Structure Type
open import Logic.Intuitionistic.Structure.ToAgda Type Type→Set


open Reify Type→Set renaming (⟦_⟧ to ⟦_⟧ᵗ)


infixr 5 _,_

data Env {ℓ} : List (Set ℓ) → Set ℓ where
  ∅   : Env ∅
  _,_ : {A : Set ℓ} {Γ : List (Set ℓ)} → A → Env Γ → Env (A , Γ)


split : ∀ {Γ Δ} → Env ⟦ Γ ++ Δ ⟧ˢ → Env ⟦ Γ ⟧ˢ × Env ⟦ Δ ⟧ˢ
split {Γ = ∅}     {Δ = Δ}      e  = (∅ , e)
split {Γ = A , Γ} {Δ = Δ} (x , e) with split {Γ} {Δ} e
... | (e₁ , e₂) = ((x , e₁) , e₂)


insert : ∀ {A} → ∀ Γ Δ → ⟦ A ⟧ᵗ → Env ⟦ Γ ++ Δ ⟧ˢ → Env ⟦ Γ ++ (A , Δ) ⟧ˢ
insert      ∅  Δ x      e  = x , e
insert (B , Γ) Δ x (y , e) = y , insert Γ Δ x e


exch : ∀ Γ Δ Σ Π → Env ⟦ (Γ ++ Δ) ++ (Σ ++ Π) ⟧ˢ → Env ⟦ (Γ ++ Σ) ++ (Δ ++ Π) ⟧ˢ
exch      ∅       ∅  Σ Π      e  = e
exch      ∅  (B , Δ) Σ Π (x , e) = insert Σ (Δ ++ Π) x (exch ∅ Δ Σ Π e)
exch (A , Γ)      Δ  Σ Π (x , e) = x , exch Γ Δ Σ Π e
