------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra      using (module Monoid)
open import Data.List    using (List; _++_; monoid) renaming (_∷_ to _,_; [] to ∅)
open import Relation.Binary.PropositionalEquality using (sym)


module Logic.Classical.Ordered.LambekGrishin.ResMon.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                Univ as LG
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement    Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base         Univ

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as Λ
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ

open Monoid (monoid Λ.Type) using (assoc)


infixr 50 ¬_

¬_ : Λ.Type → Λ.Type
¬ A = A ⇒ el ⊥


¬¬ₑ : ∀ {Γ B} → Λ Γ ⊢ B → Λ Γ ⊢ ¬ ¬ B
¬¬ₑ f = ⇒ᵢ (⇒ₑ ax f)

¬¬ᵢ : ∀ {Γ B} → Λ Γ ⊢ ¬ ¬ ¬ B → Λ Γ ⊢ ¬ B
¬¬ᵢ f = ⇒ᵢ (sᴸ (_ , ∅) (⇒ₑ f (¬¬ₑ ax)))

¬¬ˢ : ∀ {A B} → Λ A , ∅ ⊢ B → Λ ¬ B , ∅ ⊢ ¬ A
¬¬ˢ f = ⇒ᵢ (eᴸ₁ (⇒ₑ ax f))

¬¬-over-⊗ : ∀ {Γ A B} → Λ Γ ⊢ ¬ ¬ A ⊗ ¬ ¬ B → Λ Γ ⊢ ¬ ¬ (A ⊗ B)
¬¬-over-⊗ =
  ⇒ₑ (⇒ᵢ (⊗ₑᴸ₁ (⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (eᴸ₂ (⇒ₑ ax (⇒ᵢ (eᴸ₂ (⇒ₑ ax (eᴸ₁ (⊗ᵢ ax ax)))))))))))))


⌊_⌋ : LG.Type → Λ.Type
⌊ el  A ⌋ = ¬ (el A)
⌊ A ⊗ B ⌋ = ¬ (¬ ⌊ A ⌋ ⊗ ¬ ⌊ B ⌋)
⌊ A ⇒ B ⌋ =    ¬ ⌊ A ⌋ ⊗   ⌊ B ⌋
⌊ B ⇐ A ⌋ =      ⌊ B ⌋ ⊗ ¬ ⌊ A ⌋
⌊ B ⊕ A ⌋ =      ⌊ A ⌋ ⊗   ⌊ B ⌋
⌊ B ⇚ A ⌋ = ¬ (¬ ⌊ B ⌋ ⊗   ⌊ A ⌋)
⌊ A ⇛ B ⌋ = ¬ (  ⌊ A ⌋ ⊗ ¬ ⌊ B ⌋)
⌊ _     ⌋ = {!!}


mutual
  cbnᴸ : ∀ {A B} → LG A ⊢ B → Λ ¬ ¬ ⌊ B ⌋ , ∅ ⊢ ¬ ¬ ⌊ A ⌋
  cbnᴸ  ax       = ¬¬ˢ (¬¬ˢ (¬¬ˢ ax))
  cbnᴸ (m⊗  f g) = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (eᴸ₁ (⇒ₑ ax (¬¬-over-⊗ (⊗ₑᴸ₁ (⊗ᵢ (cbnᴿ f) (cbnᴿ g))))))))
  cbnᴸ (m⇒  f g) = {!!}
  cbnᴸ (m⇐  f g) = {!!}
  cbnᴸ (r⇒⊗ f)   = {!!}
  cbnᴸ (r⊗⇒ f)   = {!!}
  cbnᴸ (r⇐⊗ f)   = {!!}
  cbnᴸ (r⊗⇐ f)   = {!!}
  cbnᴸ (m⊕  f g) = {!!}
  cbnᴸ (m⇛  f g) = {!!}
  cbnᴸ (m⇚  f g) = {!!}
  cbnᴸ (r⇛⊕ f)   = {!!}
  cbnᴸ (r⊕⇛ f)   = {!!}
  cbnᴸ (r⊕⇚ f)   = {!!}
  cbnᴸ (r⇚⊕ f)   = {!!}
  cbnᴸ (d⇛⇐ f)   = {!!}
  cbnᴸ (d⇛⇒ f)   = {!!}
  cbnᴸ (d⇚⇒ f)   = {!!}
  cbnᴸ (d⇚⇐ f)   = {!!}
  cbnᴸ _         = {!!}

  cbnᴿ : ∀ {A B} → LG A ⊢ B → Λ ¬ ⌊ A ⌋ , ∅ ⊢ ¬ ¬ ¬ ⌊ B ⌋
  cbnᴿ  ax       = ¬¬ˢ (¬¬ˢ (¬¬ₑ ax))
  cbnᴿ (m⊗  f g) = {!!}
  cbnᴿ (m⇒  f g) = {!!}
  cbnᴿ (m⇐  f g) = {!!}
  cbnᴿ (r⇒⊗ f)   = {!!}
  cbnᴿ (r⊗⇒ f)   = {!!}
  cbnᴿ (r⇐⊗ f)   = {!!}
  cbnᴿ (r⊗⇐ f)   = {!!}
  cbnᴿ (m⊕  f g) = {!!}
  cbnᴿ (m⇛  f g) = {!!}
  cbnᴿ (m⇚  f g) = {!!}
  cbnᴿ (r⇛⊕ f)   = {!!}
  cbnᴿ (r⊕⇛ f)   = {!!}
  cbnᴿ (r⊕⇚ f)   = {!!}
  cbnᴿ (r⇚⊕ f)   = {!!}
  cbnᴿ (d⇛⇐ f)   = {!!}
  cbnᴿ (d⇛⇒ f)   = {!!}
  cbnᴿ (d⇚⇒ f)   = {!!}
  cbnᴿ (d⇚⇐ f)   = {!!}
  cbnᴿ _         = {!!}
