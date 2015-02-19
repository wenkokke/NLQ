------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function                                        using (_∘_)
open import Data.List                                       using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
open import Data.Product                                    using (∃; _×_; _,_)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.ToLinear {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity

PolarisedUniv : Set ℓ
PolarisedUniv = (Polarity × Univ)

open import Logic.Classical.Ordered.LambekGrishin.Type                PolarisedUniv as LGT
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      Univ          as LGTᴾ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv as LGS
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv as LGJ
open import Logic.Classical.Ordered.LambekGrishin.Base                PolarisedUniv as LGB

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as ΛT
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ as ΛB


¬_ : ΛT.Type → ΛT.Type
¬ A = A ⇒ el ⊥


mutual
  ⟦_⟧⁺ : LGT.Type → ΛT.Type
  ⟦ el (+ , A) ⟧⁺ = el A
  ⟦ el (- , A) ⟧⁺ = ¬ (¬ el A)
  ⟦     A ⊗ B  ⟧⁺ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺
  ⟦     A ⇚ B  ⟧⁺ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻
  ⟦     A ⇛ B  ⟧⁺ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺
  ⟦     A ⊕ B  ⟧⁺ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁻)
  ⟦     A ⇒ B  ⟧⁺ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻)
  ⟦     A ⇐ B  ⟧⁺ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺)

  ⟦_⟧⁻ : LGT.Type → ΛT.Type
  ⟦ el (+ , A) ⟧⁻ = ¬ el A
  ⟦ el (- , A) ⟧⁻ = ¬ el A
  ⟦     A ⊗ B  ⟧⁻ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺)
  ⟦     A ⇚ B  ⟧⁻ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻)
  ⟦     A ⇛ B  ⟧⁻ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺)
  ⟦     A ⊕ B  ⟧⁻ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁻
  ⟦     A ⇒ B  ⟧⁻ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻
  ⟦     A ⇐ B  ⟧⁻ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺


Positive-≡ : ∀ {A} → Positive A → ⟦ A ⟧⁻ ≡ ¬ ⟦ A ⟧⁺
Positive-≡ (el  A) = refl
Positive-≡ (A ⊗ B) = refl
Positive-≡ (A ⇚ B) = refl
Positive-≡ (A ⇛ B) = refl

Negative-≡ : ∀ {A} → Negative A → ⟦ A ⟧⁺ ≡ ¬ ⟦ A ⟧⁻
Negative-≡ (el  A) = refl
Negative-≡ (A ⊕ B) = refl
Negative-≡ (A ⇒ B) = refl
Negative-≡ (A ⇐ B) = refl


private

    ⟦_⟧ˢ : ∀ {p} → LGS.Structure p → List ΛT.Type
    ⟦ ·_· { + } A ⟧ˢ = ⟦ A ⟧⁺ , ∅
    ⟦ ·_· { - } A ⟧ˢ = ⟦ A ⟧⁻ , ∅
    ⟦     Γ ⊗ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
    ⟦     Γ ⇚ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
    ⟦     Γ ⇛ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
    ⟦     Γ ⊕ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
    ⟦     Γ ⇒ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
    ⟦     Γ ⇐ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ


    ⟦_⟧ᴶ : LGJ.Judgement → ΛJ.Judgement
    ⟦   X  ⊢  Y   ⟧ᴶ = ⟦ X ⟧ˢ ++ ⟦ Y ⟧ˢ ⊢ el ⊥
    ⟦ [ A ]⊢  Y   ⟧ᴶ =          ⟦ Y ⟧ˢ ⊢ ⟦ A ⟧⁻
    ⟦   X  ⊢[ B ] ⟧ᴶ = ⟦ X ⟧ˢ          ⊢ ⟦ B ⟧⁺
