------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level using (_⊔_; suc)
open import Algebra using (module Monoid)
open import Function using (id)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.List using (List; _∷_; _++_; monoid) renaming ([] to ∅)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; subst)


module Logic.Intuitionistic.Ariola {ℓ} (Univ : Set ℓ) (⫫ : Univ) where

{-
infix  1  λC_ λΠ_
infix  3  _⊢_



data Judgement : Set where
  _⊢_ : List Type → Type → Judgement





record Reify {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  infix 10 _*

  field
    _* : A → B

open Reify {{...}}

instance
  Univ→Set : Reify Univ Set
  Univ→Set = record { _* = _ᵁ }
    where
      _ᵁ : Univ → Set
      nat    ᵁ = ℕ
      string ᵁ = String
      ⫫      ᵁ = ⊥

  Type→Set : Reify Type Set
  Type→Set = record { _* = _ᵀ }
    where
      _ᵀ : Type → Set
      (el A )ᵀ =   (A)*
      (A ⇒ B)ᵀ = ¬ (B)ᵀ → ¬ (A)ᵀ
      (A - B)ᵀ = ¬ (B)ᵀ ×   (A)ᵀ

  List→Set : Reify (List Type) (List Set)
  List→Set = record { _* = _ᴸ }
    where
      _ᴸ : List Type → List Set
      ∅       ᴸ = ∅
      (A ∷ Γ) ᴸ = A * ∷ Γ ᴸ

  Judgement→Set : Reify Judgement Set₁
  Judgement→Set = record { _* = _ᴶ }
    where
      _ᴶ : Judgement → Set₁
      (Γ ⊢ A) ᴶ = Env ((¬ A *) ∷ Γ *) → ⊥

λΠ_ : Judgement → Set₁
λΠ_ = _*


private


⟦_⟧ : ∀ {Γ A} → λC Γ ⊢ A → λΠ Γ ⊢ A
⟦ refl     ⟧ (    k ∷ x ∷ ∅)         = k x
⟦ ⇒i   f   ⟧ (    k ∷ e)             = k (λ k′ x → ⟦ f ⟧ (k′ ∷ x ∷ e))
⟦ ⇒e   f g ⟧ (    k ∷ e) with split e
⟦ ⇒e   f g ⟧ (    k ∷ e) | (e₁ , e₂) = ⟦ f ⟧ ((λ k′ → ⟦ g ⟧ (k′ k ∷ e₂)) ∷ e₁)
⟦ raa  f   ⟧ (    k ∷ e)             = ⟦ f ⟧ (id ∷ (λ _ x → k x) ∷ e)
⟦ ⇒ke  f   ⟧ (_ ∷ k ∷ e)             = ⟦ f ⟧ (k id ∷ (λ _ x → k id x) ∷ e)
⟦ -i   f g ⟧ (    k ∷ e) with split e
⟦ -i   f g ⟧ (    k ∷ e) | (e₁ , e₂) = ⟦ f ⟧ ((λ x → k ((λ y → ⟦ g ⟧ (id ∷ y ∷ e₂)) , x)) ∷ e₁)
⟦ -e   f g ⟧ (    k ∷ e) with split e
⟦ -e   f g ⟧ (    k ∷ e) | (e₁ , e₂) = ⟦ f ⟧ ((λ {(x , y) → ⟦ g ⟧ (k ∷ y ∷ (λ _ → x) ∷ e₂)}) ∷ e₁)
⟦ weak f   ⟧ (    k ∷ e) with split e
⟦ weak f   ⟧ (    k ∷ e) | (e₁ , e₂) = ⟦ f ⟧ (k ∷ e₁)
⟦ cont f   ⟧ (k ∷ x ∷ e)             = ⟦ f ⟧ (k ∷ x ∷ x ∷ e)
⟦ exch {Γ} {Δ} {Σ} {Π} f ⟧ (  k ∷ e) = ⟦ f ⟧ (k ∷ exchange Γ Δ Σ Π e)
-}
