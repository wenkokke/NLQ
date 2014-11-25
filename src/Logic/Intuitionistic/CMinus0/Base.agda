------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra using (module Monoid)
open import Data.List as List using ()
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.Intuitionistic.CMinus0.Base {ℓ} (Univ : Set ℓ) (⫫ : Univ) where


open import Logic.Intuitionistic.Type              Univ as SST
open import Logic.Intuitionistic.Structure         Univ as SSS
open import Logic.Intuitionistic.CMinus0.Judgement Univ as SSJ
open Monoid (List.monoid Type) using (identity)


infix 1 λC⁻_


data λC⁻_ : Judgement → Set ℓ where
  id   : ∀ {A}
       → λC⁻ A , ∅ ⊢ A

  -- rules for implication
  ⇒i   : ∀ {Γ A B}
       → λC⁻ A , Γ ⊢     B
       → λC⁻     Γ ⊢ A ⇒ B

  ⇒e   : ∀ {Γ₁ Γ₂ A B}
       → λC⁻ Γ₁ ⊢ A ⇒ B
       → λC⁻ Γ₂ ⊢ A
       → λC⁻ Γ₁ ++ Γ₂ ⊢ B

  -- rules for subtraction
  raa  : ∀ {Γ A}
       → λC⁻ A ⇒ el ⫫ , Γ ⊢ el ⫫
       → λC⁻ Γ ⊢ A

  ⇒ke  : ∀ {Γ A}
       → λC⁻ A ⇒ el ⫫ , Γ ⊢ A
       → λC⁻ A ⇒ el ⫫ , Γ ⊢ el ⫫

  ⇛i   : ∀ {Γ₁ Γ₂ A B}
       → λC⁻     Γ₁       ⊢ A
       → λC⁻ B ,       Γ₂ ⊢ el ⫫
       → λC⁻     Γ₁ ++ Γ₂ ⊢ A ⇛ B

  ⇛e   : ∀ {Γ₁ Γ₂ A B C}
       → λC⁻                Γ₁       ⊢ A ⇛ B
       → λC⁻ A , B ⇒ el ⫫ ,       Γ₂ ⊢ C
       → λC⁻                Γ₁ ++ Γ₂ ⊢ C

  -- structural rules
  weak : ∀ Γ₂ → ∀ {Γ₁ A}
       → λC⁻ Γ₁       ⊢ A
       → λC⁻ Γ₁ ++ Γ₂ ⊢ A

  cont : ∀ {Γ A B}
       → λC⁻ A , A , Γ ⊢ B
       → λC⁻     A , Γ ⊢ B

  exch : ∀ Γ₁ Γ₂ Γ₃ Γ₄ → ∀ {A}
       → λC⁻ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢ A
       → λC⁻ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢ A


-- Variant of `exch` where the last position is empty, which is not
-- trivial to do usually due to the implementation of _++_.
XZY→XYZ : ∀ Γ₁ Γ₂ Γ₃ → ∀ {A}
      → λC⁻ (Γ₁ ++ Γ₃) ++ Γ₂ ⊢ A
      → λC⁻ (Γ₁ ++ Γ₂) ++ Γ₃ ⊢ A
XZY→XYZ Γ₁ Γ₂ Γ₃ {A} f
  = subst (λ Γ₃ → λC⁻ (Γ₁ ++ Γ₂) ++ Γ₃ ⊢ A) (Γ++∅≡Γ Γ₃) (exch Γ₁ Γ₂ Γ₃ ∅
  ( subst (λ Γ₂ → λC⁻ (Γ₁ ++ Γ₃) ++ Γ₂ ⊢ A) (sym (Γ++∅≡Γ Γ₂)) f))
  where
    Γ++∅≡Γ : ∀ Γ → Γ ++ ∅ ≡ Γ
    Γ++∅≡Γ      ∅  = refl
    Γ++∅≡Γ (A , Γ) rewrite Γ++∅≡Γ Γ = refl


-- Variant of `exch` where both the first *and* last position are
-- empty. This is a proof of the commutativity of _++_ w.r.t. the
-- ⊢-relation.
++-comm : ∀ Γ₁ Γ₂ → ∀ {A} → λC⁻ Γ₂ ++ Γ₁ ⊢ A → λC⁻ Γ₁ ++ Γ₂ ⊢ A
++-comm = XZY→XYZ ∅
