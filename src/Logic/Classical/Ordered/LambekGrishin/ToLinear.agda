------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                                         using (module Monoid)
open import Function                                        using (_∘_)
open import Data.List                                       using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
open import Data.Product                                    using (∃; _×_; _,_)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.ToLinear {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Translation

PolarisedUniv : Set ℓ
PolarisedUniv = (Polarity × Univ)

open import Logic.Classical.Ordered.LambekGrishin.Type                PolarisedUniv as LGT
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv as LGS
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv as LGJ
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      Univ          as LGTᴾ
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ          as LGB

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as ΛT
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ as ΛB
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ as ΛP
open Monoid (Data.List.monoid ΛT.Type) using (assoc)


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


    [_] : ∀ {J} → LG J → Λ ⟦ J ⟧ᴶ
    [ ax⁺         ] = ax
    [ ax⁻         ] = ax
    [ ⇁ {p = p} f ] rewrite Negative-≡ (toWitness p) = ⇒ᵢ (XA→AX [ f ])
    [ ↽ {p = p} f ] rewrite Positive-≡ (toWitness p) = ⇒ᵢ [ f ]
    [ ⇀ {p = p} f ] rewrite Positive-≡ (toWitness p) = AX→XA (⇒ₑ ax [ f ])
    [ ↼ {p = p} f ] rewrite Negative-≡ (toWitness p) = ⇒ₑ ax [ f ]
    [ ⊗ᴿ      f g ] = ⊗ᵢ [ f ] [ g ]
    [ ⇚ᴿ      f g ] = ⊗ᵢ [ f ] [ g ]
    [ ⇛ᴿ      g f ] = ⊗ᵢ [ f ] [ g ]
    [ ⊕ᴸ      f g ] = ⊗ᵢ [ f ] [ g ]
    [ ⇒ᴸ      f g ] = ⊗ᵢ [ f ] [ g ]
    [ ⇐ᴸ      g f ] = ⊗ᵢ [ f ] [ g ]
    [ ⊗ᴸ      f   ] = ⊗ₑᴸ₁ [ f ]
    [ ⇚ᴸ      f   ] = ⊗ₑᴸ₁ [ f ]
    [ ⇛ᴸ      f   ] = ⊗ₑᴸ₁ [ f ]
    [ ⊕ᴿ  {X} f   ] = ⊗ₑᴸ₂ ⟦ X ⟧ˢ [ f ]
    [ ⇒ᴿ  {X} f   ] = ⊗ₑᴸ₂ ⟦ X ⟧ˢ [ f ]
    [ ⇐ᴿ  {X} f   ] = ⊗ₑᴸ₂ ⟦ X ⟧ˢ [ f ]
    [ r⇒⊗ {X} {Y} {Z} f ] rewrite      assoc ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ  = Y[XZ]→X[YZ] ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ [ f ]
    [ r⊗⇒ {X} {Y} {Z} f ] rewrite sym (assoc ⟦ Y ⟧ˢ ⟦ X ⟧ˢ ⟦ Z ⟧ˢ) = [YX]Z→[XY]Z ⟦ Y ⟧ˢ ⟦ X ⟧ˢ ⟦ Z ⟧ˢ [ f ]
    [ r⇐⊗ {X} {Y} {Z} f ] rewrite      assoc ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ  = X[ZY]→X[YZ] ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ [ f ]
    [ r⊗⇐ {X} {Y} {Z} f ] rewrite sym (assoc ⟦ X ⟧ˢ ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ) = [XZ]Y→[XY]Z ⟦ X ⟧ˢ ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ [ f ]
    [ r⇚⊕ {X} {Y} {Z} f ] rewrite sym (assoc ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ) = [XZ]Y→[XY]Z ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ [ f ]
    [ r⊕⇚ {X} {Y} {Z} f ] rewrite      assoc ⟦ Z ⟧ˢ ⟦ X ⟧ˢ ⟦ Y ⟧ˢ  = X[ZY]→X[YZ] ⟦ Z ⟧ˢ ⟦ X ⟧ˢ ⟦ Y ⟧ˢ [ f ]
    [ r⇛⊕ {X} {Y} {Z} f ] rewrite sym (assoc ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ) = [YX]Z→[XY]Z ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ [ f ]
    [ r⊕⇛ {X} {Y} {Z} f ] rewrite      assoc ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ X ⟧ˢ  = Y[XZ]→X[YZ] ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ X ⟧ˢ [ f ]
    [ d⇛⇐ {X} {Y} {Z} {W} f ] = XYZW→ZXWY ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]
    [ d⇛⇒ {X} {Y} {Z} {W} f ] = XYZW→ZYXW ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]
    [ d⇚⇒ {X} {Y} {Z} {W} f ] = XYZW→YWXZ ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]
    [ d⇚⇐ {X} {Y} {Z} {W} f ] = XYZW→XWZY ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]


Ord→Lin : Translation LGT.Type ΛT.Type LGB.LG_ ΛB.Λ_
Ord→Lin = record { ⟦_⟧ᵀ = ⟦_⟧⁺ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
