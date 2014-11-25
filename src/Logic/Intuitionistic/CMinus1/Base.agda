------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra using (module Monoid)
open import Data.List using (monoid)


module Logic.Intuitionistic.CMinus1.Base {ℓ} (Univ : Set ℓ) (⫫ : Univ) where


open import Logic.Intuitionistic.Type                 Univ as SST
open import Logic.Intuitionistic.Structure            Univ as SSS
open import Logic.Intuitionistic.CMinus1.Judgement Univ as SSJ
open Monoid (monoid Type) using (identity)


infix 1 λC⁻_

data λC⁻_ : Judgement → Set ℓ where

  id    : ∀ {A}
        → λC⁻ A , ∅ ⊢ A ∣ ∅

  ⇒i    : ∀ {Γ Δ A B}
        → λC⁻ A , Γ ⊢     B ∣ Δ
        → λC⁻     Γ ⊢ A ⇒ B ∣ Δ

  ⇒e    : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B}
        → λC⁻ Γ₁       ⊢ A ⇒ B ∣ Δ₁
        → λC⁻       Γ₂ ⊢ A     ∣       Δ₂
        → λC⁻ Γ₁ ++ Γ₂ ⊢     B ∣ Δ₁ ++ Δ₂

  ⇛i    : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B}
        → λC⁻     Γ₁       ⊢ A     ∣ Δ₁
        → λC⁻ B ,       Γ₂ ⊢ el ⫫  ∣       Δ₂
        → λC⁻     Γ₁ ++ Γ₂ ⊢ A ⇛ B ∣ Δ₁ ++ Δ₂

  ⇛e    : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B C}
        → λC⁻     Γ₁       ⊢ A ⇛ B ∣     Δ₁
        → λC⁻ A ,       Γ₂ ⊢ C     ∣ B ,       Δ₂
        → λC⁻     Γ₁ ++ Γ₂ ⊢ C     ∣     Δ₁ ++ Δ₂

  raa   : ∀ {Γ Δ A}
        → λC⁻ Γ ⊢ el ⫫ ∣ A , Δ
        → λC⁻ Γ ⊢ A    ∣     Δ

  ⇒ke   : ∀ {Γ Δ A}
        → λC⁻ Γ ⊢ A    ∣ A , Δ
        → λC⁻ Γ ⊢ el ⫫ ∣ A , Δ

  weakl : ∀ {Γ₁} → ∀ Γ₂ → ∀ {Δ A}
        → λC⁻ Γ₁       ⊢ A ∣ Δ
        → λC⁻ Γ₁ ++ Γ₂ ⊢ A ∣ Δ

  weakr : ∀ {Γ Δ₁} → ∀ Δ₂ → ∀ {A}
        → λC⁻ Γ ⊢ A ∣ Δ₁
        → λC⁻ Γ ⊢ A ∣ Δ₁ ++ Δ₂

  contl : ∀ {Γ Δ A B}
        → λC⁻ A , A , Γ ⊢ B ∣ Δ
        → λC⁻     A , Γ ⊢ B ∣ Δ

  contr : ∀ {Γ Δ A B}
        → λC⁻ Γ ⊢ A ∣ B , B , Δ
        → λC⁻ Γ ⊢ A ∣     B , Δ

  exchl : ∀ Γ₁ Γ₂ Γ₃ Γ₄ → ∀ {Δ} → ∀ {A}
        → λC⁻ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A ∣ Δ
        → λC⁻ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A ∣ Δ

  exchr : ∀ {Γ} → ∀ Δ₁ Δ₂ Δ₃ Δ₄ → ∀ {A}
        → λC⁻ Γ ⊢ A ∣ (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
        → λC⁻ Γ ⊢ A ∣ (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
