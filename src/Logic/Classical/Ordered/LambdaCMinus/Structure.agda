------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Fin                              using (Fin; suc; zero)
open import Data.List                             using (List; _∷_; []; _++_; length)
open import Data.List.Properties                  using (length-++)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


module Logic.Classical.Ordered.LambdaCMinus.Structure {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambdaCMinus.Type Univ


data Structure : Set ℓ where

  ·_· : Type → Structure
  _⊗_ : Structure → Structure → Structure


data Context : Set ℓ where

  []   : Context
  _⊗>_ : Structure → Context → Context
  _<⊗_ : Context → Structure → Context


_[_] : Context → Structure → Structure
[]         [ Δ ] = Δ
(Γ₁ ⊗> Γ₂) [ Δ ] =  Γ₁        ⊗ (Γ₂ [ Δ ])
(Γ₁ <⊗ Γ₂) [ Δ ] = (Γ₁ [ Δ ]) ⊗  Γ₂
