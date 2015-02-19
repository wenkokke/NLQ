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
open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised      Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised PolarisedUniv
open import Logic.Classical.Ordered.LambekGrishin.Judgement           PolarisedUniv



infix 1 LG_

data LG_ : Judgement → Set ℓ where

  ax⁺   : ∀ {A}
        → LG · A · ⊢[ A ]

  abs-μ : ∀ {X A} {p : True (Negative? A)}
        → LG X ⊢ · A ·
        → LG X ⊢[  A  ]

  ⊗ᴿ    : ∀ {X Y A B}
        → LG X     ⊢[ A     ]
        → LG     Y ⊢[     B ]
        → LG X ⊗ Y ⊢[ A ⊗ B ]

  ⇚ᴿ    : ∀ {X Y A B}
        → LG   X  ⊢[ A ]
        → LG [ B ]⊢ Y
        → LG X ⇚ Y ⊢[ A ⇚ B ]

  ⇛ᴿ    : ∀ {X Y A B}
        → LG [ A ]⊢  X
        → LG   Y  ⊢[ B ]
        → LG X ⇛ Y ⊢[ A ⇛ B ]

  ax⁻   : ∀ {A}
        → LG [ A ]⊢ · A ·

  abs-̃μ : ∀ {X A} {p : True (Positive? A)}
        → LG · A · ⊢ X
        → LG [ A ]⊢ X

  ⊕ᴸ    : ∀ {X Y A B}
        → LG [ A     ]⊢     Y
        → LG [     B ]⊢ X
        → LG [ A ⊕ B ]⊢ X ⊕ Y

  ⇒ᴸ    : ∀ {X Y A B}
        → LG   X  ⊢[ A ]
        → LG [ B ]⊢  Y
        → LG [ A ⇒ B ]⊢ X ⇒ Y

  ⇐ᴸ     : ∀ {X Y A B}
         → LG [ A ]⊢  Y
         → LG   X  ⊢[ B ]
         → LG [ A ⇐ B ]⊢ Y ⇐ X


  app-μ  : ∀ {X A} {p : True (Positive? A)}
         → LG X ⊢[  A  ]
         → LG X ⊢ · A ·

  app-̃μ  : ∀ {X A} {p : True (Negative? A)}
         → LG [  A  ]⊢ X
         → LG  · A · ⊢ X

  ⊗ᴸ     : ∀ {X A B}
         → LG · A · ⊗ · B · ⊢ X
         → LG · A ⊗ B · ⊢ X

  ⇚ᴸ     : ∀ {X A B}
         → LG · A · ⇚ · B · ⊢ X
         → LG · A ⇚ B · ⊢ X

  ⇛ᴸ     : ∀ {X A B}
         → LG · A · ⇛ · B · ⊢ X
         → LG · A ⇛ B · ⊢ X

  ⊕ᴿ     : ∀ {X A B}
         → LG X ⊢ · A · ⊕ · B ·
         → LG X ⊢ · A ⊕ B ·

  ⇒ᴿ     : ∀ {X A B}
         → LG X ⊢ · A · ⇒ · B ·
         → LG X ⊢ · A ⇒ B ·

  ⇐ᴿ     : ∀ {X A B}
         → LG X ⊢ · A · ⇐ · B ·
         → LG X ⊢ · A ⇐ B ·

  res-⇒⊗ : ∀ {X Y Z}
         → LG Y ⊢ X ⇒ Z
         → LG X ⊗ Y ⊢ Z

  res-⊗⇒ : ∀ {X Y Z}
         → LG X ⊗ Y ⊢ Z
         → LG Y ⊢ X ⇒ Z

  res-⇐⊗ : ∀ {X Y Z}
         → LG X ⊢ Z ⇐ Y
         → LG X ⊗ Y ⊢ Z

  res-⊗⇐ : ∀ {X Y Z}
         → LG X ⊗ Y ⊢ Z
         → LG X ⊢ Z ⇐ Y

  res-⇚⊕ : ∀ {X Y Z}
         → LG Z ⇚ X ⊢ Y
         → LG Z ⊢ Y ⊕ X

  res-⊕⇚ : ∀ {X Y Z}
         → LG Z ⊢ Y ⊕ X
         → LG Z ⇚ X ⊢ Y

  res-⇛⊕ : ∀ {X Y Z}
         → LG Y ⇛ Z ⊢ X
         → LG Z ⊢ Y ⊕ X

  res-⊕⇛ : ∀ {X Y Z}
         → LG Z ⊢ Y ⊕ X
         → LG Y ⇛ Z ⊢ X

  grish₁ : ∀ {X Y Z W}
         → LG X ⊗ Y ⊢ Z ⊕ W
         → LG Z ⇛ X ⊢ W ⇐ Y

  grish₂ : ∀ {X Y Z W}
         → LG X ⊗ Y ⊢ Z ⊕ W
         → LG Z ⇛ Y ⊢ X ⇒ W

  grish₃ : ∀ {X Y Z W}
         → LG X ⊗ Y ⊢ Z ⊕ W
         → LG Y ⇚ W ⊢ X ⇒ Z

  grish₄ : ∀ {X Y Z W}
         → LG X ⊗ Y ⊢ Z ⊕ W
         → LG X ⇚ W ⊢ Z ⇐ Y
