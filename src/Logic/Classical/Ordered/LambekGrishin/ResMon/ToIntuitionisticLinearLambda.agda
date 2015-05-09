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



-- * Intuitionistic Linear Negation

infixr 50 ¬_

¬_ : Λ.Type → Λ.Type
¬ A = A ⇒ el ⊥


¬¬ₑ : ∀ {Γ B} → Λ Γ ⊢ B → Λ Γ ⊢ ¬ ¬ B
¬¬ₑ f = ⇒ᵢ (⇒ₑ ax f)

¬¬ᵢ : ∀ {Γ B} → Λ Γ ⊢ ¬ ¬ ¬ B → Λ Γ ⊢ ¬ B
¬¬ᵢ f = ⇒ᵢ (sᴸ (_ , ∅) (⇒ₑ f (¬¬ₑ ax)))

¬¬-swap : ∀ {A B} → Λ A , ∅ ⊢ B → Λ ¬ B , ∅ ⊢ ¬ A
¬¬-swap f = ⇒ᵢ (eᴸ₁ (⇒ₑ ax f))

¬¬A⊗¬¬B⊢¬¬[A⊗B] : ∀ {A B} → Λ ¬ ¬ A ⊗ ¬ ¬ B , ∅ ⊢ ¬ ¬ (A ⊗ B)
¬¬A⊗¬¬B⊢¬¬[A⊗B] =
  ⊗ₑ ax (⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (eᴸ₂ (⇒ₑ ax (⇒ᵢ (eᴸ₂ (⇒ₑ ax (eᴸ₁ (⊗ᵢ ax ax)))))))))))

¬¬[A⊗B]⊢¬¬A⊗¬¬B : ∀ {A B} → Λ ¬ ¬ (A ⊗ B) , ∅ ⊢ ¬ ¬ A ⊗ ¬ ¬ B
¬¬[A⊗B]⊢¬¬A⊗¬¬B {A} {B} = {!!}

¬¬-resp-⊗₁ : ∀ {Γ A B} → Λ Γ ⊢ ¬ ¬ A ⊗ ¬ ¬ B → Λ Γ ⊢ ¬ ¬ (A ⊗ B)
¬¬-resp-⊗₁ = ⇒ₑ (⇒ᵢ ¬¬A⊗¬¬B⊢¬¬[A⊗B])


-- * Call-by-Value Translation

⌈_⌉ : LG.Type → Λ.Type
⌈ el  A ⌉ = el A
⌈ A ⊗ B ⌉ =      ⌈ A ⌉ ⊗   ⌈ B ⌉
⌈ A ⇒ B ⌉ = ¬ (  ⌈ A ⌉ ⊗ ¬ ⌈ B ⌉)
⌈ B ⇐ A ⌉ = ¬ (¬ ⌈ B ⌉ ⊗   ⌈ A ⌉)
⌈ B ⊕ A ⌉ =    ¬ ⌈ B ⌉ ⊗ ¬ ⌈ A ⌉
⌈ B ⇚ A ⌉ =      ⌈ B ⌉ ⊗ ¬ ⌈ A ⌉
⌈ A ⇛ B ⌉ =    ¬ ⌈ A ⌉ ⊗   ⌈ B ⌉
⌈ _     ⌉ = {!!}


mutual
  cbvᴸ : ∀ {A B} → LG A ⊢ B → Λ ¬ ⌈ B ⌉ , ∅  ⊢ ¬ ⌈ A ⌉
  cbvᴸ  ax       = ¬¬-swap ax
  cbvᴸ (m⊗  f g) = ⇒ᵢ (⇒ₑ (¬¬-resp-⊗₁ (⊗ₑᴸ₁ (⊗ᵢ (cbvᴿ f) (cbvᴿ g)))) ax)
  cbvᴸ (m⇒  f g) = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (¬¬-resp-⊗₁ (⊗ₑᴸ₁ (⊗ᵢ (cbvᴿ f) (¬¬ₑ (cbvᴸ g))))) ax))))
  cbvᴸ (m⇐  f g) = ⇒ᵢ (eᴸ₁ (⇒ₑ ax (⇒ᵢ (⇒ₑ (¬¬-resp-⊗₁ (⊗ₑᴸ₁ (⊗ᵢ (¬¬ₑ (cbvᴸ f)) (cbvᴿ g)))) ax))))
  cbvᴸ (r⇒⊗ f)   = {!!}
  cbvᴸ (r⊗⇒ f)   = {!!}
  cbvᴸ (r⇐⊗ f)   = {!!}
  cbvᴸ (r⊗⇐ f)   = {!!}
  cbvᴸ (m⊕  f g) = {!!}
  cbvᴸ (m⇛  f g) = {!!}
  cbvᴸ (m⇚  f g) = {!!}
  cbvᴸ (r⇛⊕ f)   = {!!}
  cbvᴸ (r⊕⇛ f)   = {!!}
  cbvᴸ (r⊕⇚ f)   = {!!}
  cbvᴸ (r⇚⊕ f)   = {!!}
  cbvᴸ (d⇛⇐ f)   = {!!}
  cbvᴸ (d⇛⇒ f)   = {!!}
  cbvᴸ (d⇚⇒ f)   = {!!}
  cbvᴸ (d⇚⇐ f)   = {!!}
  cbvᴸ _         = {!!}

  cbvᴿ : ∀ {A B} → LG A ⊢ B → Λ ⌈ A ⌉ , ∅  ⊢ ¬ ¬ ⌈ B ⌉
  cbvᴿ  ax       = {!!}
  cbvᴿ (m⊗  f g) = {!!}
  cbvᴿ (m⇒  f g) = {!!}
  cbvᴿ (m⇐  f g) = {!!}
  cbvᴿ (r⇒⊗ f)   = {!!}
  cbvᴿ (r⊗⇒ f)   = {!!}
  cbvᴿ (r⇐⊗ f)   = {!!}
  cbvᴿ (r⊗⇐ f)   = {!!}
  cbvᴿ (m⊕  f g) = {!!}
  cbvᴿ (m⇛  f g) = {!!}
  cbvᴿ (m⇚  f g) = {!!}
  cbvᴿ (r⇛⊕ f)   = {!!}
  cbvᴿ (r⊕⇛ f)   = {!!}
  cbvᴿ (r⊕⇚ f)   = {!!}
  cbvᴿ (r⇚⊕ f)   = {!!}
  cbvᴿ (d⇛⇐ f)   = {!!}
  cbvᴿ (d⇛⇒ f)   = {!!}
  cbvᴿ (d⇚⇒ f)   = {!!}
  cbvᴿ (d⇚⇐ f)   = {!!}
  cbvᴿ _         = {!!}


-- * Call-by-Name Translation

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
  cbnᴸ  ax       = ¬¬-swap (¬¬-swap (¬¬-swap ax))
  cbnᴸ (m⊗  f g) = ⇒ᵢ (⇒ₑ ax (⇒ᵢ (eᴸ₁ (⇒ₑ ax (¬¬-resp-⊗₁ (⊗ₑ ax (⊗ᵢ (cbnᴿ f) (cbnᴿ g))))))))
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
  cbnᴿ  ax       = ¬¬-swap (¬¬-swap (¬¬ₑ ax))
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
