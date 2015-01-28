open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Fin                              using (Fin; suc; zero)
open import Data.List                             using (List; _∷_; []; _++_; length)
open import Data.List.Properties                  using (length-++)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)


module Logic.Structure.Conjunction {ℓ} (Univ : Set ℓ) where


open import Logic.Type Univ


data Conjunction : Set ℓ where

  ·_· : Type → Conjunction
  _⊗_ : Conjunction → Conjunction → Conjunction


data Context : Set ℓ where

  []   : Context
  _⊗>_ : Conjunction → Context → Context
  _<⊗_ : Context → Conjunction → Context


_[_] : Context → Conjunction → Conjunction
[]         [ Δ ] = Δ
(Γ₁ ⊗> Γ₂) [ Δ ] =  Γ₁        ⊗ (Γ₂ [ Δ ])
(Γ₁ <⊗ Γ₂) [ Δ ] = (Γ₁ [ Δ ]) ⊗  Γ₂


⌊_⌋ : Conjunction → Type
⌊ · A · ⌋ =       A
⌊ Γ ⊗ Δ ⌋ = ⌊ Γ ⌋ ⊗ ⌊ Δ ⌋

⌈_⌉ : Type → Conjunction
⌈ A ⊗ B ⌉ = ⌈ A ⌉ ⊗ ⌈ B ⌉
⌈   A   ⌉ =     · A ·
