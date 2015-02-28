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


module Logic.Classical.Ordered.LambekGrishin.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity

PolarisedUniv : Set ℓ
PolarisedUniv = (Polarity × Univ)

open import Logic.Classical.Ordered.LambekGrishin.Type                PolarisedUniv
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      Univ


infix 1 LG_

data LG_ : Judgement → Set ℓ where

  -- axioms
  ax⁺ : ∀ {A}
      → LG · A · ⊢[ A ]

  ax⁻ : ∀ {A}
      → LG [ A ]⊢ · A ·

  -- focus right and left
  ⇁   : ∀ {X A} {p : True (Negative? A)}
      → LG X ⊢ · A ·
      → LG X ⊢[  A  ]

  ↽   : ∀ {X A} {p : True (Positive? A)}
      → LG  · A · ⊢ X
      → LG [  A  ]⊢ X

  -- defocus right and left
  ⇀   : ∀ {X A} {p : True (Positive? A)}
      → LG X ⊢[  A  ]
      → LG X ⊢ · A ·

  ↼   : ∀ {X A} {p : True (Negative? A)}
      → LG [  A  ]⊢ X
      → LG  · A · ⊢ X

  -- structural rules
  ◇ᴸ  : ∀ {Y A}
      → LG ⟨ ·   A · ⟩ ⊢ Y
      → LG   · ◇ A ·   ⊢ Y

  ◇ᴿ  : ∀ {X B}
      → LG   X   ⊢[   B ]
      → LG ⟨ X ⟩ ⊢[ ◇ B ]

  □ᴸ  : ∀ {A Y}
      → LG [   A ]⊢   Y
      → LG [ □ A ]⊢ [ Y ]

  □ᴿ  : ∀ {X A}
      → LG X ⊢ [ ·   A · ]
      → LG X ⊢   · □ A ·

  ₀ᴸ  : ∀ {X A}
      → LG     X  ⊢[   A ]
      → LG [ ₀ A ]⊢  ₀ X

  ₀ᴿ  : ∀ {X A}
      → LG X ⊢ ₀ · A ·
      → LG X ⊢ · ₀ A ·

  ⁰ᴸ  : ∀ {X A}
      → LG   X    ⊢[ A   ]
      → LG [ A ⁰ ]⊢  X ⁰

  ⁰ᴿ  : ∀ {X A}
      → LG X ⊢ · A · ⁰
      → LG X ⊢ · A ⁰ ·

  ₁ᴸ  : ∀ {Y A}
      → LG ₁ · A · ⊢ Y
      → LG · ₁ A · ⊢ Y

  ₁ᴿ  : ∀ {Y A}
      → LG [   A ]⊢    Y
      → LG   ₁ Y  ⊢[ ₁ A ]

  ¹ᴸ  : ∀ {Y A}
      → LG · A · ¹ ⊢ Y
      → LG · A ¹ · ⊢ Y

  ¹ᴿ  : ∀ {Y A}
      → LG [ A   ]⊢  Y
      → LG   Y ¹  ⊢[ A ¹ ]

  ⊗ᴿ  : ∀ {X Y A B}
      → LG X ⊢[ A ]
      → LG Y ⊢[ B ]
      → LG X ⊗ Y ⊢[ A ⊗ B ]

  ⇚ᴿ  : ∀ {X Y A B}
      → LG X ⊢[ A ]
      → LG [ B ]⊢ Y
      → LG X ⇚ Y ⊢[ A ⇚ B ]

  ⇛ᴿ  : ∀ {X Y A B}
      → LG X ⊢[ A ]
      → LG [ B ]⊢ Y
      → LG Y ⇛ X ⊢[ B ⇛ A ]

  ⊕ᴸ  : ∀ {X Y A B}
      → LG [ B ]⊢ Y
      → LG [ A ]⊢ X
      → LG [ B ⊕ A ]⊢ Y ⊕ X

  ⇒ᴸ  : ∀ {X Y A B}
      → LG X ⊢[ A ]
      → LG [ B ]⊢ Y
      → LG [ A ⇒ B ]⊢ X ⇒ Y

  ⇐ᴸ  : ∀ {X Y A B}
      → LG X ⊢[ A ]
      → LG [ B ]⊢ Y
      → LG [ B ⇐ A ]⊢ Y ⇐ X

  ⊗ᴸ  : ∀ {Y A B}
      → LG · A · ⊗ · B · ⊢ Y
      → LG · A   ⊗   B · ⊢ Y

  ⇚ᴸ  : ∀ {X A B}
      → LG · A · ⇚ · B · ⊢ X
      → LG · A   ⇚   B · ⊢ X

  ⇛ᴸ  : ∀ {X A B}
      → LG · B · ⇛ · A · ⊢ X
      → LG · B   ⇛   A · ⊢ X

  ⊕ᴿ  : ∀ {X A B}
      → LG X ⊢ · B · ⊕ · A ·
      → LG X ⊢ · B   ⊕   A ·

  ⇒ᴿ  : ∀ {X A B}
      → LG X ⊢ · A · ⇒ · B ·
      → LG X ⊢ · A   ⇒   B ·

  ⇐ᴿ  : ∀ {X A B}
      → LG X ⊢ · B · ⇐ · A ·
      → LG X ⊢ · B   ⇐   A ·

  -- residuation rules for (□ , ◇)
  r□◇ : ∀ {X Y}
      → LG   X   ⊢ [ Y ]
      → LG ⟨ X ⟩ ⊢   Y

  r◇□ : ∀ {X Y}
      → LG ⟨ X ⟩ ⊢   Y
      → LG   X   ⊢ [ Y ]

  -- residuation rules for (₀ , ⁰ , ₁ , ¹)
  r⁰₀ : ∀ {X Y}
      → LG X ⊢ Y ⁰
      → LG Y ⊢ ₀ X

  r₀⁰ : ∀ {X Y}
      → LG Y ⊢ ₀ X
      → LG X ⊢ Y ⁰

  r¹₁ : ∀ {X Y}
      → LG X ¹ ⊢ Y
      → LG ₁ Y ⊢ X

  r₁¹ : ∀ {X Y}
      → LG ₁ Y ⊢ X
      → LG X ¹ ⊢ Y

  -- residuation rules for (⇐ , ⊗ , ⇒)
  r⇒⊗ : ∀ {X Y Z}
      → LG Y ⊢ X ⇒ Z
      → LG X ⊗ Y ⊢ Z

  r⊗⇒ : ∀ {X Y Z}
      → LG X ⊗ Y ⊢ Z
      → LG Y ⊢ X ⇒ Z

  r⇐⊗ : ∀ {X Y Z}
      → LG X ⊢ Z ⇐ Y
      → LG X ⊗ Y ⊢ Z

  r⊗⇐ : ∀ {X Y Z}
      → LG X ⊗ Y ⊢ Z
      → LG X ⊢ Z ⇐ Y

  -- residuation rules for (⇚ , ⊕ , ⇛)
  r⇚⊕ : ∀ {X Y Z}
      → LG Z ⇚ X ⊢ Y
      → LG Z ⊢ Y ⊕ X

  r⊕⇚ : ∀ {X Y Z}
      → LG Z ⊢ Y ⊕ X
      → LG Z ⇚ X ⊢ Y

  r⇛⊕ : ∀ {X Y Z}
      → LG Y ⇛ Z ⊢ X
      → LG Z ⊢ Y ⊕ X

  r⊕⇛ : ∀ {X Y Z}
      → LG Z ⊢ Y ⊕ X
      → LG Y ⇛ Z ⊢ X

  -- grishin interaction principes
  d⇛⇐ : ∀ {X Y Z W}
      → LG X ⊗ Y ⊢ Z ⊕ W
      → LG Z ⇛ X ⊢ W ⇐ Y

  d⇛⇒ : ∀ {X Y Z W}
      → LG X ⊗ Y ⊢ Z ⊕ W
      → LG Z ⇛ Y ⊢ X ⇒ W

  d⇚⇒ : ∀ {X Y Z W}
      → LG X ⊗ Y ⊢ Z ⊕ W
      → LG Y ⇚ W ⊢ X ⇒ Z

  d⇚⇐ : ∀ {X Y Z W}
      → LG X ⊗ Y ⊢ Z ⊕ W
      → LG X ⇚ W ⊢ Z ⇐ Y
