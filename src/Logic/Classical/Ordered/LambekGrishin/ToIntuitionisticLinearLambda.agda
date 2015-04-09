------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                                         using (module Monoid)
open import Function                                        using (_∘_; const)
open import Data.List                                       using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.LambekGrishin.Type             Univ           as LGT
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised   Univ (const +) as LGP
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Judgement Univ           as LGJ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base      Univ           as LG

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as ΛT
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ as Λ
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ as ΛP
open Monoid (Data.List.monoid ΛT.Type) using (assoc)


infix 50 ¬_

¬_ : ΛT.Type → ΛT.Type
¬ A = A ⇒ el ⊥

m⊗′ : ∀ {A B C D} → Λ A , ∅ ⊢ B → Λ C , ∅ ⊢ D → Λ A ⊗ C , ∅ ⊢ B ⊗ D
m⊗′ f g = ⊗ₑᴸ₁ (⊗ᵢ f g)

m⇒′ : ∀ {A B C D} → Λ A , ∅ ⊢ B → Λ C , ∅ ⊢ D → Λ B ⇒ C , ∅ ⊢ A ⇒ D
m⇒′ f g = ⇒ᵢ (⇒ₑ (⇒ᵢ g) (eᴸ₁ (⇒ₑ ax f)))


mutual
  ⟦_⟧⁺ : LGT.Type → ΛT.Type
  ⟦ el  A ⟧⁺ = el A
  ⟦ □   A ⟧⁺ = ¬  ⟦ A ⟧⁻
  ⟦ ◇   A ⟧⁺ =    ⟦ A ⟧⁺
  ⟦ ₀   A ⟧⁺ = ¬  ⟦ A ⟧⁺
  ⟦ A   ⁰ ⟧⁺ = ¬  ⟦ A ⟧⁺
  ⟦ ₁   A ⟧⁺ =    ⟦ A ⟧⁻
  ⟦ A   ¹ ⟧⁺ =    ⟦ A ⟧⁻
  ⟦ A ⊗ B ⟧⁺ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺
  ⟦ A ⇚ B ⟧⁺ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻
  ⟦ A ⇛ B ⟧⁺ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺
  ⟦ A ⊕ B ⟧⁺ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁻)
  ⟦ A ⇒ B ⟧⁺ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻)
  ⟦ A ⇐ B ⟧⁺ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺)

  ⟦_⟧⁻ : LGT.Type → ΛT.Type
  ⟦ el  A ⟧⁻ = ¬ el A
  ⟦ □   A ⟧⁻ =    ⟦ A ⟧⁻
  ⟦ ◇   A ⟧⁻ = ¬  ⟦ A ⟧⁺
  ⟦ ₀   A ⟧⁻ =    ⟦ A ⟧⁺
  ⟦ A   ⁰ ⟧⁻ =    ⟦ A ⟧⁺
  ⟦ ₁   A ⟧⁻ = ¬  ⟦ A ⟧⁻
  ⟦ A   ¹ ⟧⁻ = ¬  ⟦ A ⟧⁻
  ⟦ A ⊗ B ⟧⁻ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺)
  ⟦ A ⇚ B ⟧⁻ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻)
  ⟦ A ⇛ B ⟧⁻ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺)
  ⟦ A ⊕ B ⟧⁻ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁻
  ⟦ A ⇒ B ⟧⁻ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻
  ⟦ A ⇐ B ⟧⁻ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺


Positive-≡ : ∀ {A} → Positive A → ⟦ A ⟧⁻ ≡ ¬ ⟦ A ⟧⁺
Positive-≡ (el  A) = refl
Positive-≡ (◇   A) = refl
Positive-≡ (₁   A) = refl
Positive-≡ (A   ¹) = refl
Positive-≡ (A ⊗ B) = refl
Positive-≡ (A ⇚ B) = refl
Positive-≡ (A ⇛ B) = refl

Negative-≡ : ∀ {A} → Negative A → ⟦ A ⟧⁺ ≡ ¬ ⟦ A ⟧⁻
Negative-≡ (el  A {{()}})
Negative-≡ (□   A) = refl
Negative-≡ (₀   A) = refl
Negative-≡ (A   ⁰) = refl
Negative-≡ (A ⊕ B) = refl
Negative-≡ (A ⇒ B) = refl
Negative-≡ (A ⇐ B) = refl


[_] : ∀ {A B} → LG A ⊢ B → Λ ⟦ A ⟧⁺ , ⟦ B ⟧⁻ , ∅ ⊢ el ⊥
[ ax      ] = {!!}
[ m□  f   ] = {!!}
[ m◇  f   ] = {!!}
[ r□◇ f   ] = {!!}
[ r◇□ f   ] = {!!}
[ m⁰  f   ] = {!!}
[ m₀  f   ] = {!!}
[ r⁰₀ f   ] = {!!}
[ r₀⁰ f   ] = {!!}
[ m₁  f   ] = {!!}
[ m¹  f   ] = {!!}
[ r¹₁ f   ] = {!!}
[ r₁¹ f   ] = {!!}
[ m⊗  f g ] = {!!}
[ m⇒  f g ] = {!!}
[ m⇐  f g ] = {!!}
[ r⇒⊗ f   ] = {!!}
[ r⊗⇒ f   ] = {!!}
[ r⇐⊗ f   ] = {!!}
[ r⊗⇐ f   ] = {!!}
[ m⊕  f g ] = {!!}
[ m⇛  f g ] = {!!}
[ m⇚  f g ] = {!!}
[ r⇛⊕ f   ] = {!!}
[ r⊕⇛ f   ] = {!!}
[ r⊕⇚ f   ] = {!!}
[ r⇚⊕ f   ] = {!!}
[ d⇛⇐ f   ] = {!!}
[ d⇛⇒ f   ] = {!!}
[ d⇚⇒ f   ] = {!!}
[ d⇚⇐ f   ] = {!!}
