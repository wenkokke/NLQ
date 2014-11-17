------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Algebra using (module Monoid)
open import Data.List using (monoid)


module Logic.Intuitionistic.Subtractive.Base {ℓ} (Univ : Set ℓ) (⫫ : Univ) where


open import Logic.Intuitionistic.Type      Univ as SST
open import Logic.Intuitionistic.Structure Univ as SSS
open import Logic.Intuitionistic.Judgement Univ as SSJ
open Monoid (monoid Type) using (identity)


infix 1 λC_


data λC_ : Judgement → Set ℓ where
  id   : ∀ {A}
       → λC A , ∅ ⊢ A

  -- rules for implication
  ⇒i   : ∀ {Γ A B}
       → λC A , Γ ⊢ B → λC Γ ⊢ A ⇒ B
  ⇒e   : ∀ {Γ Δ A B}
       → λC Γ ⊢ A ⇒ B → λC Δ ⊢ A → λC Γ ++ Δ ⊢ B

  -- rules for subtraction
  raa  : ∀ {Γ A}
       → λC A ⇒ el ⫫ , Γ ⊢ el ⫫ → λC Γ ⊢ A
  ⇒ke  : ∀ {Γ A}
       → λC A ⇒ el ⫫ , Γ ⊢ A → λC A ⇒ el ⫫ , Γ ⊢ el ⫫
  ⇛i   : ∀ {Γ Δ A B}
       → λC Γ ⊢ A → λC B , Δ ⊢ el ⫫ → λC Γ ++ Δ ⊢ A ⇛ B
  ⇛e   : ∀ {Γ Δ A B C}
       → λC Γ ⊢ A ⇛ B → λC A , B ⇒ el ⫫ , Δ ⊢ C → λC Γ ++ Δ ⊢ C

  -- structural rules
  weak : ∀ {Γ Δ A}
       → λC Γ ⊢ A → λC Γ ++ Δ ⊢ A
  cont : ∀ {Γ A B}
       → λC A , A , Γ ⊢ B → λC A , Γ ⊢ B
  exch : ∀ Γ Δ Σ Π → ∀ {A}
       → λC (Γ ++ Σ) ++ (Δ ++ Π) ⊢ A → λC (Γ ++ Δ) ++ (Σ ++ Π) ⊢ A
