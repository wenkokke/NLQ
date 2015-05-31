------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                                         using (module Monoid)
open import Function                                        using (_∘_)
open import Data.List                                       using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
open import Data.Product                                    using (∃; _×_; _,_; proj₁)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.FocPol.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Translation

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as ΛT
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ as ΛB
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ as ΛP

open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      (Polarity × Univ) proj₁ as LGTᴾ
open import Logic.Classical.Ordered.LambekGrishin.Type                (Polarity × Univ) as LGT
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised (Polarity × Univ) as LGS
open import Logic.Classical.Ordered.LambekGrishin.Judgement           (Polarity × Univ) as LGJ
open import Logic.Classical.Ordered.LambekGrishin.FocPol.Base         Univ          as LGB

open Monoid (Data.List.monoid ΛT.Type) using (assoc)


¬_ : ΛT.Type → ΛT.Type
¬ A = A ⇒ el ⊥


mutual
  ⟦_⟧⁺ : LGT.Type → ΛT.Type
  ⟦ el (+ , A) ⟧⁺ = el A
  ⟦ el (- , A) ⟧⁺ = ¬ (¬ el A)
  ⟦     □   A  ⟧⁺ = ¬  ⟦ A ⟧⁻
  ⟦     ◇   A  ⟧⁺ =    ⟦ A ⟧⁺
  ⟦     ₀   A  ⟧⁺ = ¬  ⟦ A ⟧⁺
  ⟦     A   ⁰  ⟧⁺ = ¬  ⟦ A ⟧⁺
  ⟦     ₁   A  ⟧⁺ =    ⟦ A ⟧⁻
  ⟦     A   ¹  ⟧⁺ =    ⟦ A ⟧⁻
  ⟦     A ⊗ B  ⟧⁺ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺
  ⟦     A ⇚ B  ⟧⁺ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻
  ⟦     A ⇛ B  ⟧⁺ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺
  ⟦     A ⊕ B  ⟧⁺ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁻)
  ⟦     A ⇒ B  ⟧⁺ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻)
  ⟦     A ⇐ B  ⟧⁺ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺)

  ⟦_⟧⁻ : LGT.Type → ΛT.Type
  ⟦ el (+ , A) ⟧⁻ = ¬ el A
  ⟦ el (- , A) ⟧⁻ = ¬ el A
  ⟦     □   A  ⟧⁻ =    ⟦ A ⟧⁻
  ⟦     ◇   A  ⟧⁻ = ¬  ⟦ A ⟧⁺
  ⟦     ₀   A  ⟧⁻ =    ⟦ A ⟧⁺
  ⟦     A   ⁰  ⟧⁻ =    ⟦ A ⟧⁺
  ⟦     ₁   A  ⟧⁻ = ¬  ⟦ A ⟧⁻
  ⟦     A   ¹  ⟧⁻ = ¬  ⟦ A ⟧⁻
  ⟦     A ⊗ B  ⟧⁻ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁺)
  ⟦     A ⇚ B  ⟧⁻ = ¬ (⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻)
  ⟦     A ⇛ B  ⟧⁻ = ¬ (⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺)
  ⟦     A ⊕ B  ⟧⁻ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁻
  ⟦     A ⇒ B  ⟧⁻ =    ⟦ A ⟧⁺ ⊗ ⟦ B ⟧⁻
  ⟦     A ⇐ B  ⟧⁻ =    ⟦ A ⟧⁻ ⊗ ⟦ B ⟧⁺



Positive-≡ : ∀ {A} → Positive A → ⟦ A ⟧⁻ ≡ ¬ ⟦ A ⟧⁺
Positive-≡ (el (+ , A) {{A⁺}}) = refl
Positive-≡ (el (- , A) {{()}})
Positive-≡ (◇   A) = refl
Positive-≡ (₁   A) = refl
Positive-≡ (A   ¹) = refl
Positive-≡ (A ⊗ B) = refl
Positive-≡ (A ⇚ B) = refl
Positive-≡ (A ⇛ B) = refl

Negative-≡ : ∀ {A} → Negative A → ⟦ A ⟧⁺ ≡ ¬ ⟦ A ⟧⁻
Negative-≡ (el (+ , A) {{()}})
Negative-≡ (el (- , A) {{A⁻}}) = refl
Negative-≡ (□   A) = refl
Negative-≡ (₀   A) = refl
Negative-≡ (A   ⁰) = refl
Negative-≡ (A ⊕ B) = refl
Negative-≡ (A ⇒ B) = refl
Negative-≡ (A ⇐ B) = refl


⟦_⟧ˢ : ∀ {p} → LGS.Structure p → List ΛT.Type
⟦ ·_· { + } A ⟧ˢ = ⟦ A ⟧⁺ , ∅
⟦ ·_· { - } A ⟧ˢ = ⟦ A ⟧⁻ , ∅
⟦     [ Γ ]   ⟧ˢ = ⟦ Γ ⟧ˢ
⟦     ⟨ Γ ⟩   ⟧ˢ = ⟦ Γ ⟧ˢ
⟦     ₀   Γ   ⟧ˢ = ⟦ Γ ⟧ˢ
⟦     Γ   ⁰   ⟧ˢ = ⟦ Γ ⟧ˢ
⟦     ₁   Γ   ⟧ˢ = ⟦ Γ ⟧ˢ
⟦     Γ   ¹   ⟧ˢ = ⟦ Γ ⟧ˢ
⟦     Γ ⊗ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
⟦     Γ ⇚ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
⟦     Γ ⇛ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
⟦     Γ ⊕ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
⟦     Γ ⇒ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ
⟦     Γ ⇐ Δ   ⟧ˢ = ⟦ Γ ⟧ˢ ++ ⟦ Δ ⟧ˢ

private

    ⟦_⟧ᴶ : LGJ.Judgement → ΛJ.Judgement
    ⟦   X  ⊢  Y   ⟧ᴶ = ⟦ X ⟧ˢ ++ ⟦ Y ⟧ˢ ⊢ el ⊥
    ⟦ [ A ]⊢  Y   ⟧ᴶ =          ⟦ Y ⟧ˢ ⊢ ⟦ A ⟧⁻
    ⟦   X  ⊢[ B ] ⟧ᴶ = ⟦ X ⟧ˢ          ⊢ ⟦ B ⟧⁺


    [_]ᵀ : ∀ {J} → LG J → Λ ⟦ J ⟧ᴶ
    [ ax⁺         ]ᵀ = ax
    [ ax⁻         ]ᵀ = ax
    [ ⇁ {p = p} f ]ᵀ rewrite Negative-≡ (toWitness p) = ⇒ᵢ (XA→AX [ f ]ᵀ)
    [ ↽ {p = p} f ]ᵀ rewrite Positive-≡ (toWitness p) = ⇒ᵢ [ f ]ᵀ
    [ ⇀ {p = p} f ]ᵀ rewrite Positive-≡ (toWitness p) = AX→XA (⇒ₑ ax [ f ]ᵀ)
    [ ↼ {p = p} f ]ᵀ rewrite Negative-≡ (toWitness p) = ⇒ₑ ax [ f ]ᵀ
    [ □ᴸ      f   ]ᵀ = [ f ]ᵀ
    [ □ᴿ      f   ]ᵀ = [ f ]ᵀ
    [ ◇ᴸ      f   ]ᵀ = [ f ]ᵀ
    [ ◇ᴿ      f   ]ᵀ = [ f ]ᵀ
    [ ₀ᴸ      f   ]ᵀ = [ f ]ᵀ
    [ ₀ᴿ      f   ]ᵀ = [ f ]ᵀ
    [ ⁰ᴸ      f   ]ᵀ = [ f ]ᵀ
    [ ⁰ᴿ      f   ]ᵀ = [ f ]ᵀ
    [ ₁ᴸ      f   ]ᵀ = [ f ]ᵀ
    [ ₁ᴿ      f   ]ᵀ = [ f ]ᵀ
    [ ¹ᴸ      f   ]ᵀ = [ f ]ᵀ
    [ ¹ᴿ      f   ]ᵀ = [ f ]ᵀ
    [ ⊗ᴿ      f g ]ᵀ = ⊗ᵢ [ f ]ᵀ [ g ]ᵀ
    [ ⇚ᴿ      f g ]ᵀ = ⊗ᵢ [ f ]ᵀ [ g ]ᵀ
    [ ⇛ᴿ      g f ]ᵀ = ⊗ᵢ [ f ]ᵀ [ g ]ᵀ
    [ ⊕ᴸ      f g ]ᵀ = ⊗ᵢ [ f ]ᵀ [ g ]ᵀ
    [ ⇒ᴸ      f g ]ᵀ = ⊗ᵢ [ f ]ᵀ [ g ]ᵀ
    [ ⇐ᴸ      g f ]ᵀ = ⊗ᵢ [ f ]ᵀ [ g ]ᵀ
    [ ⊗ᴸ      f   ]ᵀ = ⊗ₑᴸ₁ [ f ]ᵀ
    [ ⇚ᴸ      f   ]ᵀ = ⊗ₑᴸ₁ [ f ]ᵀ
    [ ⇛ᴸ      f   ]ᵀ = ⊗ₑᴸ₁ [ f ]ᵀ
    [ ⊕ᴿ  {X} f   ]ᵀ = ⊗ₑᴸ₂ ⟦ X ⟧ˢ [ f ]ᵀ
    [ ⇒ᴿ  {X} f   ]ᵀ = ⊗ₑᴸ₂ ⟦ X ⟧ˢ [ f ]ᵀ
    [ ⇐ᴿ  {X} f   ]ᵀ = ⊗ₑᴸ₂ ⟦ X ⟧ˢ [ f ]ᵀ
    [ r□◇ {X} {Y} f ]ᵀ = [ f ]ᵀ
    [ r◇□ {X} {Y} f ]ᵀ = [ f ]ᵀ
    [ r₀⁰ {X} {Y} f ]ᵀ = sᴸ ⟦ X ⟧ˢ [ f ]ᵀ
    [ r⁰₀ {X} {Y} f ]ᵀ = sᴸ ⟦ Y ⟧ˢ [ f ]ᵀ
    [ r₁¹ {X} {Y} f ]ᵀ = sᴸ ⟦ X ⟧ˢ [ f ]ᵀ
    [ r¹₁ {X} {Y} f ]ᵀ = sᴸ ⟦ Y ⟧ˢ [ f ]ᵀ
    [ r⇒⊗ {X} {Y} {Z} f ]ᵀ rewrite      assoc ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ  = Y[XZ]→X[YZ] ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ [ f ]ᵀ
    [ r⊗⇒ {X} {Y} {Z} f ]ᵀ rewrite sym (assoc ⟦ Y ⟧ˢ ⟦ X ⟧ˢ ⟦ Z ⟧ˢ) = [YX]Z→[XY]Z ⟦ Y ⟧ˢ ⟦ X ⟧ˢ ⟦ Z ⟧ˢ [ f ]ᵀ
    [ r⇐⊗ {X} {Y} {Z} f ]ᵀ rewrite      assoc ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ  = X[ZY]→X[YZ] ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ [ f ]ᵀ
    [ r⊗⇐ {X} {Y} {Z} f ]ᵀ rewrite sym (assoc ⟦ X ⟧ˢ ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ) = [XZ]Y→[XY]Z ⟦ X ⟧ˢ ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ [ f ]ᵀ
    [ r⇚⊕ {X} {Y} {Z} f ]ᵀ rewrite sym (assoc ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ) = [XZ]Y→[XY]Z ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ [ f ]ᵀ
    [ r⊕⇚ {X} {Y} {Z} f ]ᵀ rewrite      assoc ⟦ Z ⟧ˢ ⟦ X ⟧ˢ ⟦ Y ⟧ˢ  = X[ZY]→X[YZ] ⟦ Z ⟧ˢ ⟦ X ⟧ˢ ⟦ Y ⟧ˢ [ f ]ᵀ
    [ r⇛⊕ {X} {Y} {Z} f ]ᵀ rewrite sym (assoc ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ) = [YX]Z→[XY]Z ⟦ Z ⟧ˢ ⟦ Y ⟧ˢ ⟦ X ⟧ˢ [ f ]ᵀ
    [ r⊕⇛ {X} {Y} {Z} f ]ᵀ rewrite      assoc ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ X ⟧ˢ  = Y[XZ]→X[YZ] ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ X ⟧ˢ [ f ]ᵀ
    [ d⇛⇐ {X} {Y} {Z} {W} f ]ᵀ = XYZW→ZXWY ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]ᵀ
    [ d⇛⇒ {X} {Y} {Z} {W} f ]ᵀ = XYZW→ZYXW ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]ᵀ
    [ d⇚⇒ {X} {Y} {Z} {W} f ]ᵀ = XYZW→YWXZ ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]ᵀ
    [ d⇚⇐ {X} {Y} {Z} {W} f ]ᵀ = XYZW→XWZY ⟦ X ⟧ˢ ⟦ Y ⟧ˢ ⟦ Z ⟧ˢ ⟦ W ⟧ˢ [ f ]ᵀ


LG→LL : Translation LGT.Type ΛT.Type LGB.LG_ ΛB.Λ_
LG→LL = record { ⟦_⟧ᵀ = ⟦_⟧⁺ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_]ᵀ }
