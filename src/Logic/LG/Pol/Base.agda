------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function                              using (_∘_)
open import Data.List                             using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Data.Product                          using (∃; _×_; proj₁)
open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Logic.Polarity


module Logic.LG.Pol.Base {ℓ} (Atom : Set ℓ) (Polarityᴬ? : Atom → Polarity) where


open import Logic.LG.Type.Polarised      Atom Polarityᴬ?
open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Judgement           Atom


infix 1 fLG_
infix 2 _⊢fLG_ [_]⊢fLG_ _⊢fLG[_]


mutual
  _⊢fLG_ : Structure + → Structure - → Set ℓ
  X ⊢fLG Y = fLG X ⊢ Y

  _⊢fLG[_] : Structure + → Type → Set ℓ
  X ⊢fLG[ B ] = fLG X ⊢[ B ]

  [_]⊢fLG_ : Type → Structure - → Set ℓ
  [ A ]⊢fLG Y = fLG [ A ]⊢ Y

  data fLG_ : Judgement → Set ℓ where

    ax⁺ : ∀ {A} → · A · ⊢fLG[ A ]
    ax⁻ : ∀ {A} → [ A ]⊢fLG · A ·

    ⇁   : ∀ {A X} {p : True (Negative? A)} → X ⊢fLG · A · → X ⊢fLG[  A  ]
    ↽   : ∀ {A X} {p : True (Positive? A)} →  · A · ⊢fLG X → [  A  ]⊢fLG X
    ⇀   : ∀ {A X} {p : True (Positive? A)} → X ⊢fLG[  A  ] → X ⊢fLG · A ·
    ↼   : ∀ {A X} {p : True (Negative? A)} → [  A  ]⊢fLG X →  · A · ⊢fLG X

    ◇ᴸ  : ∀ {Y A}     →  ⟨ · A · ⟩ ⊢fLG Y → · ◇ A · ⊢fLG Y
    ◇ᴿ  : ∀ {X B}     →  X ⊢fLG[ B ] → ⟨ X ⟩ ⊢fLG[ ◇ B ]
    □ᴸ  : ∀ {A Y}     →  [ A ]⊢fLG Y → [ □ A ]⊢fLG [ Y ]
    □ᴿ  : ∀ {X A}     →  X ⊢fLG [ · A · ] → X ⊢fLG · □ A ·
    r□◇ : ∀ {X Y}     →  X ⊢fLG [ Y ] → ⟨ X ⟩ ⊢fLG Y
    r◇□ : ∀ {X Y}     →  ⟨ X ⟩ ⊢fLG Y → X ⊢fLG [ Y ]

    ₀ᴸ  : ∀ {X A}     →  X ⊢fLG[ A ] → [ ₀ A ]⊢fLG ₀ X
    ₀ᴿ  : ∀ {X A}     →  X ⊢fLG ₀ · A · → X ⊢fLG · ₀ A ·
    ⁰ᴸ  : ∀ {X A}     →  X ⊢fLG[ A ] → [ A ⁰ ]⊢fLG X ⁰
    ⁰ᴿ  : ∀ {X A}     →  X ⊢fLG · A · ⁰ → X ⊢fLG · A ⁰ ·
    ₁ᴸ  : ∀ {Y A}     →  ₁ · A · ⊢fLG Y → · ₁ A · ⊢fLG Y
    ₁ᴿ  : ∀ {Y A}     →  [ A ]⊢fLG Y → ₁ Y ⊢fLG[ ₁ A ]
    ¹ᴸ  : ∀ {Y A}     →  · A · ¹ ⊢fLG Y → · A ¹ · ⊢fLG Y
    ¹ᴿ  : ∀ {Y A}     →  [ A ]⊢fLG Y → Y ¹ ⊢fLG[ A ¹ ]
    r⁰₀ : ∀ {X Y}     →  X ⊢fLG Y ⁰ → Y ⊢fLG ₀ X
    r₀⁰ : ∀ {X Y}     →  Y ⊢fLG ₀ X → X ⊢fLG Y ⁰
    r¹₁ : ∀ {X Y}     →  X ¹ ⊢fLG Y → ₁ Y ⊢fLG X
    r₁¹ : ∀ {X Y}     →  ₁ Y ⊢fLG X → X ¹ ⊢fLG Y

    ⊗ᴸ  : ∀ {Y A B}   →  · A · ⊗ · B · ⊢fLG Y → · A ⊗ B · ⊢fLG Y
    ⊗ᴿ  : ∀ {X Y A B} →  X ⊢fLG[ A ] → Y ⊢fLG[ B ] → X ⊗ Y ⊢fLG[ A ⊗ B ]
    ⇒ᴸ  : ∀ {X Y A B} →  X ⊢fLG[ A ] → [ B ]⊢fLG Y → [ A ⇒ B ]⊢fLG X ⇒ Y
    ⇒ᴿ  : ∀ {X A B}   →  X ⊢fLG · A · ⇒ · B · → X ⊢fLG · A ⇒ B ·
    ⇐ᴸ  : ∀ {X Y A B} →  X ⊢fLG[ A ] → [ B ]⊢fLG Y → [ B ⇐ A ]⊢fLG Y ⇐ X
    ⇐ᴿ  : ∀ {X A B}   →  X ⊢fLG · B · ⇐ · A · → X ⊢fLG · B ⇐ A ·
    r⇒⊗ : ∀ {X Y Z}   →  Y ⊢fLG X ⇒ Z → X ⊗ Y ⊢fLG Z
    r⊗⇒ : ∀ {X Y Z}   →  X ⊗ Y ⊢fLG Z → Y ⊢fLG X ⇒ Z
    r⇐⊗ : ∀ {X Y Z}   →  X ⊢fLG Z ⇐ Y → X ⊗ Y ⊢fLG Z
    r⊗⇐ : ∀ {X Y Z}   →  X ⊗ Y ⊢fLG Z → X ⊢fLG Z ⇐ Y

    ⊕ᴸ   : ∀ {X Y A B} →  [ B ]⊢fLG Y →  [ A ]⊢fLG X →  [ B ⊕ A ]⊢fLG Y ⊕ X
    ⊕ᴿ   : ∀ {X A B}   →  X ⊢fLG · B · ⊕ · A · →  X ⊢fLG · B ⊕ A ·
    ⇚ᴸ   : ∀ {X A B}   →  · A · ⇚ · B · ⊢fLG X →  · A ⇚ B · ⊢fLG X
    ⇚ᴿ   : ∀ {X Y A B} →  X ⊢fLG[ A ] →  [ B ]⊢fLG Y →  X ⇚ Y ⊢fLG[ A ⇚ B ]
    ⇛ᴸ   : ∀ {X A B}   →  · B · ⇛ · A · ⊢fLG X →  · B ⇛ A · ⊢fLG X
    ⇛ᴿ   : ∀ {X Y A B} →  X ⊢fLG[ A ] →  [ B ]⊢fLG Y →  Y ⇛ X ⊢fLG[ B ⇛ A ]
    r⇚⊕  : ∀ {X Y Z}   →  Z ⇚ X ⊢fLG Y →  Z ⊢fLG Y ⊕ X
    r⊕⇚  : ∀ {X Y Z}   →  Z ⊢fLG Y ⊕ X →  Z ⇚ X ⊢fLG Y
    r⇛⊕  : ∀ {X Y Z}   →  Y ⇛ Z ⊢fLG X →  Z ⊢fLG Y ⊕ X
    r⊕⇛  : ∀ {X Y Z}   →  Z ⊢fLG Y ⊕ X →  Y ⇛ Z ⊢fLG X

    d⇛⇐  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  Z ⇛ X ⊢fLG W ⇐ Y
    d⇛⇒  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  Z ⇛ Y ⊢fLG X ⇒ W
    d⇚⇒  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  Y ⇚ W ⊢fLG X ⇒ Z
    d⇚⇐  : ∀ {X Y Z W} →  X ⊗ Y ⊢fLG Z ⊕ W →  X ⇚ W ⊢fLG Z ⇐ Y
