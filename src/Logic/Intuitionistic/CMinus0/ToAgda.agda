------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level using (suc)
open import Function using (const)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Logic.Reification


module Logic.Intuitionistic.CMinus0.ToAgda
       {ℓ₁ ℓ₂}
       (Univ : Set ℓ₁)
       (Univ→Set : Reify Univ (Set ℓ₂))
       (⫫ : Univ)
       (⫫→⊥ : ⟦ ⫫ ⟧ → ⊥)
       where


open import Logic.Intuitionistic.Type              Univ
open import Logic.Intuitionistic.Structure         Type
open import Logic.Intuitionistic.CMinus0.Judgement Univ
open import Logic.Intuitionistic.CMinus0.Base      Univ ⫫


⟦_⟧ᵗ : Type → Set ℓ₂
⟦ el A  ⟧ᵗ = ⟦ A ⟧
⟦ A ⇒ B ⟧ᵗ = ¬  ⟦ B ⟧ᵗ → ¬ ⟦ A ⟧ᵗ
⟦ A ⇛ B ⟧ᵗ = ¬  ⟦ B ⟧ᵗ ×   ⟦ A ⟧ᵗ
⟦ A ⊗ B ⟧ᵗ = ¬ (⟦ B ⟧ᵗ ×   ⟦ A ⟧ᵗ)


instance
  Type→Set : Reify Type (Set ℓ₂)
  Type→Set = record { ⟦_⟧ = ⟦_⟧ᵗ }


open import Logic.Intuitionistic.Structure.ToAgda Type Type→Set
open import Logic.Intuitionistic.Agda.Environment Type Type→Set as Env


⟦_⟧ʲ : Judgement → Set ℓ₂
⟦ Γ ⊢ A ⟧ʲ = Env ((¬ ⟦ A ⟧ᵗ) , ⟦ Γ ⟧ˢ) → ⊥


instance
  Judgement→Set : Reify Judgement (Set ℓ₂)
  Judgement→Set = record { ⟦_⟧ = ⟦_⟧ʲ }


infix 3 λΠ_

λΠ_ : Judgement → Set ℓ₂
λΠ J = ⟦ J ⟧

instance
  λC⁻→λΠ : ∀ {J} → Reify (λC⁻ J) (λΠ J)
  λC⁻→λΠ = record { ⟦_⟧ = [_] }
    where
    go : ∀ {Γ A} → λC⁻ Γ ⊢ A → λΠ Γ ⊢ A
    go id               (k , (x , ∅))             = k x
    go (⇒i   f)         (k ,      e )             = k (λ k′ x → go f (k′ , (x , e)))
    go (⇒e   f g)       (x ,      e ) with Env.split e
    go (⇒e   f g)       (x ,      e ) | (e₁ , e₂) = go f ((λ k → go g (k x , e₂)) , e₁)
    go (raa  f)         (k ,      e )             = go f (⫫→⊥ , (const k , e))
    go (⇒ke  f)         (_ , (k , e))             = go f (k ⫫→⊥ , (const (k ⫫→⊥) , e))
    go (⇛i   f g)       (k ,      e ) with Env.split e
    go (⇛i   f g)       (k ,      e ) | (e₁ , e₂) = go f ((λ x → k ((λ y → go g (⫫→⊥ , (y , e₂))) , x)) , e₁)
    go (⇛e   f g)       (k ,      e ) with Env.split e
    go (⇛e   f g)       (k ,      e ) | (e₁ , e₂) = go f ((λ {(x , y) → go g (k , (y , (const x , e₂)))}) , e₁)
    go (weak f)         (k ,      e ) with Env.split e
    go (weak f)         (k ,      e ) | (e₁ , e₂) = go f (k , e₁)
    go (cont f)         (k , (x , e))             = go f (k , (x , (x , e)))
    go (exch Γ Δ Σ Π f) (k ,      e )             = go f (k , Env.exch Γ Δ Σ Π e)

    [_] : ∀ {J} → λC⁻ J → λΠ J
    [_] {Γ ⊢ A} = go {Γ} {A}
