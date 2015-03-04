------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                                         using (module Monoid)
open import Function                                        using (_∘_)
open import Data.List                                       using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                                        using (_⊎_; inj₁; inj₂)
open import Data.Product                                    using (∃; _×_; _,_)
open import Data.Unit                                       using (tt)
open import Relation.Nullary                                using (Dec; yes; no)
open import Relation.Nullary.Decidable                      using (True; toWitness)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_; refl; sym; cong)


module Logic.Classical.Ordered.LambekGrishin.ToClassicalLinearLambekGrishin {ℓ} (Univ : Set ℓ) (⊥ : Univ) where


open import Logic.Polarity
open import Logic.Translation

PolarisedUniv : Set ℓ
PolarisedUniv = (Polarity × Univ)

open import Logic.Classical.Ordered.LambekGrishin.Type                PolarisedUniv as OT
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv as OS
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv as OJ
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      Univ          as OP
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ          as O  hiding (PolarisedUniv)

open import Logic.Classical.Linear.LambekGrishin.Type                PolarisedUniv as LT
open import Logic.Classical.Linear.LambekGrishin.Structure.Polarised PolarisedUniv as LS
open import Logic.Classical.Linear.LambekGrishin.Judgement           PolarisedUniv as LJ
open import Logic.Classical.Linear.LambekGrishin.Type.Polarised      Univ          as LP
open import Logic.Classical.Linear.LambekGrishin.Base                Univ          as L


private
  ⟦_⟧ᵀ : OT.Type → LT.Type
  ⟦ el A  ⟧ᵀ = el  A
  ⟦ □  A  ⟧ᵀ = □ ⟦ A ⟧ᵀ
  ⟦ ◇  A  ⟧ᵀ = ◇ ⟦ A ⟧ᵀ
  ⟦ ₀  A  ⟧ᵀ = ₀ ⟦ A ⟧ᵀ
  ⟦ A  ⁰  ⟧ᵀ = ⟦ A ⟧ᵀ ⁰
  ⟦ ₁  A  ⟧ᵀ = ₁ ⟦ A ⟧ᵀ
  ⟦ A  ¹  ⟧ᵀ = ⟦ A ⟧ᵀ ¹
  ⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ
  ⟦ B ⇐ A ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ
  ⟦ A ⇚ B ⟧ᵀ = ⟦ A ⟧ᵀ ⇚ ⟦ B ⟧ᵀ
  ⟦ B ⇛ A ⟧ᵀ = ⟦ A ⟧ᵀ ⇚ ⟦ B ⟧ᵀ
  ⟦ A ⊗ B ⟧ᵀ = ⟦ A ⟧ᵀ ⊗ ⟦ B ⟧ᵀ
  ⟦ A ⊕ B ⟧ᵀ = ⟦ A ⟧ᵀ ⊕ ⟦ B ⟧ᵀ

  ⟦_⟧ˢ : ∀ {p} → OS.Structure p → LS.Structure p
  ⟦ · A · ⟧ˢ = · ⟦ A ⟧ᵀ ·
  ⟦ [ X ] ⟧ˢ =  [ ⟦ X ⟧ˢ ]
  ⟦ ⟨ X ⟩ ⟧ˢ =  ⟨ ⟦ X ⟧ˢ ⟩
  ⟦ ₀   X ⟧ˢ =  ₀   ⟦ X ⟧ˢ
  ⟦ X   ⁰ ⟧ˢ =  ⟦ X ⟧ˢ   ⁰
  ⟦ ₁   X ⟧ˢ =  ₁   ⟦ X ⟧ˢ
  ⟦ X   ¹ ⟧ˢ =  ⟦ X ⟧ˢ   ¹
  ⟦ X ⊗ Y ⟧ˢ =  ⟦ X ⟧ˢ ⊗ ⟦ Y ⟧ˢ
  ⟦ X ⇚ Y ⟧ˢ =  ⟦ X ⟧ˢ ⇚ ⟦ Y ⟧ˢ
  ⟦ X ⇛ Y ⟧ˢ =  ⟦ Y ⟧ˢ ⇚ ⟦ X ⟧ˢ
  ⟦ X ⊕ Y ⟧ˢ =  ⟦ X ⟧ˢ ⊕ ⟦ Y ⟧ˢ
  ⟦ X ⇒ Y ⟧ˢ =  ⟦ X ⟧ˢ ⇒ ⟦ Y ⟧ˢ
  ⟦ X ⇐ Y ⟧ˢ =  ⟦ Y ⟧ˢ ⇒ ⟦ X ⟧ˢ

  ⟦_⟧ᴶ : OJ.Judgement → LJ.Judgement
  ⟦   X  ⊢  Y   ⟧ᴶ =   ⟦ X ⟧ˢ ⊢ ⟦ Y ⟧ˢ
  ⟦ [ A ]⊢  Y   ⟧ᴶ = [ ⟦ A ⟧ᵀ ]⊢ ⟦ Y ⟧ˢ
  ⟦   X  ⊢[ B ] ⟧ᴶ =   ⟦ X ⟧ˢ ⊢[ ⟦ B ⟧ᵀ ]

  ⟦Positive_⟧ : ∀ {A} → True (OP.Positive? A) → True (LP.Positive? ⟦ A ⟧ᵀ)
  ⟦Positive_⟧ {el (+ , A)} p = p
  ⟦Positive_⟧ {el (- , A)} p = p
  ⟦Positive_⟧ {□ A}        p = p
  ⟦Positive_⟧ {◇ A}        p = p
  ⟦Positive_⟧ {₀ A}        p = p
  ⟦Positive_⟧ {A ⁰}        p = p
  ⟦Positive_⟧ {₁ A}        p = p
  ⟦Positive_⟧ {A ¹}        p = p
  ⟦Positive_⟧ {A ⇒ B}      p = p
  ⟦Positive_⟧ {A ⇐ B}      p = p
  ⟦Positive_⟧ {A ⇚ B}      p = p
  ⟦Positive_⟧ {A ⇛ B}      p = p
  ⟦Positive_⟧ {A ⊗ B}      p = p
  ⟦Positive_⟧ {A ⊕ B}      p = p

  ⟦Negative_⟧ : ∀ {A} → True (OP.Negative? A) → True (LP.Negative? ⟦ A ⟧ᵀ)
  ⟦Negative_⟧ {el (+ , A)} p = p
  ⟦Negative_⟧ {el (- , A)} p = p
  ⟦Negative_⟧ {□ A}        p = p
  ⟦Negative_⟧ {◇ A}        p = p
  ⟦Negative_⟧ {₀ A}        p = p
  ⟦Negative_⟧ {A ⁰}        p = p
  ⟦Negative_⟧ {₁ A}        p = p
  ⟦Negative_⟧ {A ¹}        p = p
  ⟦Negative_⟧ {A ⇒ B}      p = p
  ⟦Negative_⟧ {A ⇐ B}      p = p
  ⟦Negative_⟧ {A ⇚ B}      p = p
  ⟦Negative_⟧ {A ⇛ B}      p = p
  ⟦Negative_⟧ {A ⊗ B}      p = p
  ⟦Negative_⟧ {A ⊕ B}      p = p

  toLLG : ∀ {J} → O.LG J → L.LG ⟦ J ⟧ᴶ
  toLLG ax⁺ = ax⁺
  toLLG ax⁻ = ax⁻
  toLLG (⇁ {p = p} f) = ⇁ {p = ⟦Negative p ⟧} (toLLG f)
  toLLG (↽ {p = p} f) = ↽ {p = ⟦Positive p ⟧} (toLLG f)
  toLLG (⇀ {p = p} f) = ⇀ {p = ⟦Positive p ⟧} (toLLG f)
  toLLG (↼ {p = p} f) = ↼ {p = ⟦Negative p ⟧} (toLLG f)
  toLLG (◇ᴸ  f  ) = ◇ᴸ (toLLG f)
  toLLG (◇ᴿ  f  ) = ◇ᴿ (toLLG f)
  toLLG (□ᴸ  f  ) = □ᴸ (toLLG f)
  toLLG (□ᴿ  f  ) = □ᴿ (toLLG f)
  toLLG (₀ᴸ  f  ) = ₀ᴸ (toLLG f)
  toLLG (₀ᴿ  f  ) = ₀ᴿ (toLLG f)
  toLLG (⁰ᴸ  f  ) = ⁰ᴸ (toLLG f)
  toLLG (⁰ᴿ  f  ) = ⁰ᴿ (toLLG f)
  toLLG (₁ᴸ  f  ) = ₁ᴸ (toLLG f)
  toLLG (₁ᴿ  f  ) = ₁ᴿ (toLLG f)
  toLLG (¹ᴸ  f  ) = ¹ᴸ (toLLG f)
  toLLG (¹ᴿ  f  ) = ¹ᴿ (toLLG f)
  toLLG (⊗ᴿ  f g) = ⊗ᴿ (toLLG f) (toLLG g)
  toLLG (⇚ᴿ  f g) = ⇚ᴿ (toLLG f) (toLLG g)
  toLLG (⇛ᴿ  f g) = ⇚ᴿ (toLLG f) (toLLG g)
  toLLG (⊕ᴸ  f g) = ⊕ᴸ (toLLG f) (toLLG g)
  toLLG (⇒ᴸ  f g) = ⇒ᴸ (toLLG f) (toLLG g)
  toLLG (⇐ᴸ  f g) = ⇒ᴸ (toLLG f) (toLLG g)
  toLLG (⊗ᴸ  f  ) = ⊗ᴸ (toLLG f)
  toLLG (⇚ᴸ  f  ) = ⇚ᴸ (toLLG f)
  toLLG (⇛ᴸ  f  ) = ⇚ᴸ (toLLG f)
  toLLG (⊕ᴿ  f  ) = ⊕ᴿ (toLLG f)
  toLLG (⇒ᴿ  f  ) = ⇒ᴿ (toLLG f)
  toLLG (⇐ᴿ  f  ) = ⇒ᴿ (toLLG f)
  toLLG (r□◇ f  ) = r□◇ (toLLG f)
  toLLG (r◇□ f  ) = r◇□ (toLLG f)
  toLLG (r⁰₀ f  ) = r⁰₀ (toLLG f)
  toLLG (r₀⁰ f  ) = r₀⁰ (toLLG f)
  toLLG (r¹₁ f  ) = r¹₁ (toLLG f)
  toLLG (r₁¹ f  ) = r₁¹ (toLLG f)
  toLLG (r⇒⊗ f  ) = r⇒⊗ (toLLG f)
  toLLG (r⊗⇒ f  ) = r⊗⇒ (toLLG f)
  toLLG (r⇐⊗ f  ) = ⊗ᶜ (r⇒⊗ (toLLG f))
  toLLG (r⊗⇐ f  ) = r⊗⇒ (⊗ᶜ (toLLG f))
  toLLG (r⇚⊕ f  ) = r⇚⊕ (toLLG f)
  toLLG (r⊕⇚ f  ) = r⊕⇚ (toLLG f)
  toLLG (r⇛⊕ f  ) = ⊕ᶜ (r⇚⊕ (toLLG f))
  toLLG (r⊕⇛ f  ) = r⊕⇚ (⊕ᶜ (toLLG f))
  toLLG (d⇛⇐ f  ) = d⇚⇒ (toLLG f)
  toLLG (d⇛⇒ f  ) = d⇚⇒ (⊗ᶜ (toLLG f))
  toLLG (d⇚⇒ f  ) = d⇚⇒ (⊗ᶜ (⊕ᶜ (toLLG f)))
  toLLG (d⇚⇐ f  ) = d⇚⇒ (⊕ᶜ (toLLG f))


Ord→Lin : Translation OT.Type LT.Type O.LG_ L.LG_
Ord→Lin = record
  { ⟦_⟧ᵀ = ⟦_⟧ᵀ
  ; ⟦_⟧ᴶ = ⟦_⟧ᴶ
  ; [_]  = toLLG
  }
