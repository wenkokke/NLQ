------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- λC⁻-calculus in Parigot's style, which I am guessing is strictly
-- less expressive than when formulated in Prawitz's style.
--
-- TODO: Drop out the left structural rules, rename ⇛ to -, add the
-- product and the left implication.
------------------------------------------------------------------------


open import Algebra using (module Monoid)
open import Data.List using (monoid)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; subst)


module Logic.Intuitionistic.CMinus1.Base {ℓ} (Univ : Set ℓ) (⫫ : Univ) where


open import Logic.Intuitionistic.Type                 Univ as SST
open import Logic.Intuitionistic.Structure            Univ as SSS
open import Logic.Intuitionistic.CMinus1.Judgement Univ as SSJ
open Monoid (monoid Type) using (identity; assoc)


infix 1 λC⁻_

data λC⁻_ : Judgement → Set ℓ where

  id    : ∀ {A}
        → λC⁻ A , ∅ ⊢ el ⫫ ∣ A , ∅

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


XZY→XYZᴸ : ∀ Γ₁ Γ₂ Γ₃ → ∀ {A Δ}
         → λC⁻ (Γ₁ ++ Γ₃) ++ Γ₂ ⊢ A ∣ Δ
         → λC⁻ (Γ₁ ++ Γ₂) ++ Γ₃ ⊢ A ∣ Δ
XZY→XYZᴸ Γ₁ Γ₂ Γ₃ {A} {Δ} f =
  subst (λ Γ₃ → λC⁻ (Γ₁ ++ Γ₂) ++ Γ₃ ⊢ A ∣ Δ) (proj₂ identity Γ₃) (
  exchl Γ₁ Γ₂ Γ₃ ∅ (
  subst (λ Γ₂ → λC⁻ (Γ₁ ++ Γ₃) ++ Γ₂ ⊢ A ∣ Δ) (sym (proj₂ identity Γ₂))
  f))

++-commᴸ : ∀ Γ₁ Γ₂ → ∀ {A Δ}
         → λC⁻ Γ₂ ++ Γ₁ ⊢ A ∣ Δ
         → λC⁻ Γ₁ ++ Γ₂ ⊢ A ∣ Δ
++-commᴸ = XZY→XYZᴸ ∅


XZY→XYZᴿ : ∀ {Γ A} → ∀ Δ₁ Δ₂ Δ₃
         → λC⁻ Γ ⊢ A ∣ (Δ₁ ++ Δ₃) ++ Δ₂
         → λC⁻ Γ ⊢ A ∣ (Δ₁ ++ Δ₂) ++ Δ₃
XZY→XYZᴿ {Γ} {A} Δ₁ Δ₂ Δ₃ f =
  subst (λ Δ₃ → λC⁻ Γ ⊢ A ∣ (Δ₁ ++ Δ₂) ++ Δ₃) (proj₂ identity Δ₃) (
  exchr Δ₁ Δ₂ Δ₃ ∅ (
  subst (λ Δ₂ → λC⁻ Γ ⊢ A ∣ (Δ₁ ++ Δ₃) ++ Δ₂) (sym (proj₂ identity Δ₂))
  f))

++-commᴿ : ∀ {Γ A} → ∀ Δ₁ Δ₂
         → λC⁻ Γ ⊢ A ∣ Δ₂ ++ Δ₁
         → λC⁻ Γ ⊢ A ∣ Δ₁ ++ Δ₂
++-commᴿ = XZY→XYZᴿ ∅
