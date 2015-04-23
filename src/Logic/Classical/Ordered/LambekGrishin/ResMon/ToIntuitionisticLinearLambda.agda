------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra      using (module Monoid)
open import Data.List    using (List; _++_; monoid) renaming (_∷_ to _,_; [] to ∅)
open import Relation.Binary.PropositionalEquality using (sym)


module Logic.Classical.Ordered.LambekGrishin.ResMon.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Classical.Ordered.LambekGrishin.Type             Univ as LG
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Univ

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as Λ
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ

open Monoid (monoid Λ.Type) using (assoc)


infixr 50 ¬_

¬_ : Λ.Type → Λ.Type
¬ A = A ⇒ el ⊥

¬¬¬→¬ : ∀ {A} → Λ ¬ ¬ ¬ A , ∅ ⊢ ¬ A
¬¬¬→¬ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ ax ax))))


⌈_⌉ : LG.Type → Λ.Type
⌈ el  A ⌉ = el A
⌈ A ⊗ B ⌉ =      ⌈ A ⌉ ⊗   ⌈ B ⌉
⌈ A ⇒ B ⌉ = ¬ (  ⌈ A ⌉ ⊗ ¬ ⌈ B ⌉)
⌈ B ⇐ A ⌉ = ¬ (¬ ⌈ B ⌉ ⊗   ⌈ A ⌉)
⌈ A ⊕ B ⌉ = {!!}
⌈ B ⇚ A ⌉ =      ⌈ B ⌉ ⊗ ¬ ⌈ A ⌉
⌈ A ⇛ B ⌉ =    ¬ ⌈ A ⌉ ⊗   ⌈ B ⌉
⌈ _     ⌉ = {!!}

⌊_⌋ : LG.Type → Λ.Type
⌊ A ⌋ = ⌈ A ∞ ⌉


mutual
  ⌈_⌉ᴸ : ∀ {A B} → LG A ⊢ B → Λ ¬ ⌈ B ⌉ , ∅ ⊢ ¬ ⌈ A ⌉
  ⌈ ax      ⌉ᴸ = ⇒ᵢ (eᴸ₁ (⇒ₑ ax ax))
  ⌈ m⊗  f g ⌉ᴸ = {!!}
  ⌈ m⇒  f g ⌉ᴸ = {!!}
  ⌈ m⇐  f g ⌉ᴸ = {!!}
  ⌈ r⇒⊗ f   ⌉ᴸ = {!!}
  ⌈ r⊗⇒ f   ⌉ᴸ = {!!}
  ⌈ r⇐⊗ f   ⌉ᴸ = {!!}
  ⌈ r⊗⇐ f   ⌉ᴸ = {!!}
  ⌈ m⊕  f g ⌉ᴸ = {!!}
  ⌈ m⇛  f g ⌉ᴸ = {!!}
  ⌈ m⇚  f g ⌉ᴸ = {!!}
  ⌈ r⇛⊕ f   ⌉ᴸ = {!!}
  ⌈ r⊕⇛ f   ⌉ᴸ = {!!}
  ⌈ r⊕⇚ f   ⌉ᴸ = {!!}
  ⌈ r⇚⊕ f   ⌉ᴸ = {!!}
  ⌈ d⇛⇐ f   ⌉ᴸ = {!!}
  ⌈ d⇛⇒ f   ⌉ᴸ = {!!}
  ⌈ d⇚⇒ f   ⌉ᴸ = {!!}
  ⌈ d⇚⇐ f   ⌉ᴸ = {!!}
  ⌈ _       ⌉ᴸ = {!!}

  ⌈_⌉ᴿ : ∀ {A B} → LG A ⊢ B → Λ ⌈ A ⌉ , ∅ ⊢ ¬ ¬ ⌈ B ⌉
  ⌈ ax      ⌉ᴿ = ⇒ᵢ (⇒ₑ ax ax)
  ⌈ m⊗  f g ⌉ᴿ = {!!}
  ⌈ m⇒  f g ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (    (⇒ₑ ⌈ f ⌉ᴿ (⇒ᵢ (    (eᴸ₂ (⇒ₑ ax (⊗ᵢ ax ⌈ g ⌉ᴸ))))))))))
  ⌈ m⇐  f g ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₁ (⇒ₑ ⌈ g ⌉ᴿ (⇒ᵢ (eᴸ₁ (eᴸ₂ (⇒ₑ ax (⊗ᵢ ⌈ f ⌉ᴸ ax))))))))))
  ⌈ r⇒⊗ f   ⌉ᴿ = ⊗ₑᴸ₁ (⇒ᵢ (eᴸ₁ (⊗ᵢᴸ₁ (eᴸ₁ (⇒ₑ (⇒ₑ (⇒ᵢ ¬¬¬→¬) ⌈ f ⌉ᴿ) ax)))))
  ⌈ r⊗⇒ f   ⌉ᴿ = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (⊗ₑᴸ₁ (eᴸ₁ (eᴸ₂ (eᴸ₂ (⇒ₑ (⊗ᵢᴸ₁ ⌈ f ⌉ᴿ) ax)))))))
  ⌈ r⇐⊗ f   ⌉ᴿ = {!!}
  ⌈ r⊗⇐ f   ⌉ᴿ = {!!}
  ⌈ m⊕  f g ⌉ᴿ = {!!}
  ⌈ m⇛  f g ⌉ᴿ = {!!}
  ⌈ m⇚  f g ⌉ᴿ = {!!}
  ⌈ r⇛⊕ f   ⌉ᴿ = {!!}
  ⌈ r⊕⇛ f   ⌉ᴿ = {!!}
  ⌈ r⊕⇚ f   ⌉ᴿ = {!!}
  ⌈ r⇚⊕ f   ⌉ᴿ = {!!}
  ⌈ d⇛⇐ f   ⌉ᴿ = {!!}
  ⌈ d⇛⇒ f   ⌉ᴿ = {!!}
  ⌈ d⇚⇒ f   ⌉ᴿ = {!!}
  ⌈ d⇚⇐ f   ⌉ᴿ = {!!}
  ⌈ _       ⌉ᴿ = {!!}
