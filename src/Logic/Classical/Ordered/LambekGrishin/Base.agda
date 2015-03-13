------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Why are `⇀` and `↼` included?
--
--   While the defocussing rules (⇀ , ↼) can be derived using cut,
--   the suggested procedure for "cut elimination" leaves some cuts in
--   the derivation---namely, those cuts with axiomatic premises. This
--   means that we, in effect, take an axiomatisation where we have the
--   rule `cut` instead of `⇀` and `↼`, but restrict it to only allow
--   for axiomatic premises (i.e. `cut ax⁺ _` and `cut _ ax⁻`)... which
--   in reality is the same axiomatisation, but more cumbersome.
--
------------------------------------------------------------------------


open import Function using (_∘_)


module Logic.Classical.Ordered.LambekGrishin.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ
open import Logic.Classical.Ordered.LambekGrishin.Judgement           Univ


infix 1 LG_

data LG_ : Judgement → Set ℓ where

  -- axioms
  ax⁺ : ∀ {A}       → LG · A · ⊢[ A ]
  ax⁻ : ∀ {A}       → LG [ A ]⊢ · A ·

  -- focus right and left
  ⇁   : ∀ {X A}     → LG X ⊢ · A · → LG X ⊢[ A ]
  ↽   : ∀ {X A}     → LG · A · ⊢ X → LG [ A ]⊢ X

  -- defocus right and left
  ⇀   : ∀ {X A}     → LG X ⊢[ A ] → LG X ⊢ · A ·
  ↼   : ∀ {X A}     → LG [ A ]⊢ X → LG · A · ⊢ X

  -- rules for (□ , ◇)
  ◇ᴸ  : ∀ {Y A}     → LG ⟨ · A · ⟩ ⊢ Y → LG · ◇ A · ⊢ Y
  ◇ᴿ  : ∀ {X B}     → LG X ⊢[ B ] → LG ⟨ X ⟩ ⊢[ ◇ B ]
  □ᴸ  : ∀ {A Y}     → LG [ A ]⊢ Y → LG [ □ A ]⊢ [ Y ]
  □ᴿ  : ∀ {X A}     → LG X ⊢ [ · A · ] → LG X ⊢ · □ A ·
  r□◇ : ∀ {X Y}     → LG X ⊢ [ Y ] → LG ⟨ X ⟩ ⊢ Y
  r◇□ : ∀ {X Y}     → LG ⟨ X ⟩ ⊢ Y → LG X ⊢ [ Y ]

  --  rules for (₀ , ⁰ , ₁ , ¹)
  ₀ᴸ  : ∀ {X A}     → LG X ⊢[ A ] → LG [ ₀ A ]⊢ ₀ X
  ₀ᴿ  : ∀ {X A}     → LG X ⊢ ₀ · A · → LG X ⊢ · ₀ A ·
  ⁰ᴸ  : ∀ {X A}     → LG X ⊢[ A ] → LG [ A ⁰ ]⊢ X ⁰
  ⁰ᴿ  : ∀ {X A}     → LG X ⊢ · A · ⁰ → LG X ⊢ · A ⁰ ·
  ₁ᴸ  : ∀ {Y A}     → LG ₁ · A · ⊢ Y → LG · ₁ A · ⊢ Y
  ₁ᴿ  : ∀ {Y A}     → LG [ A ]⊢ Y → LG ₁ Y ⊢[ ₁ A ]
  ¹ᴸ  : ∀ {Y A}     → LG · A · ¹ ⊢ Y → LG · A ¹ · ⊢ Y
  ¹ᴿ  : ∀ {Y A}     → LG [ A ]⊢ Y → LG Y ¹ ⊢[ A ¹ ]
  r⁰₀ : ∀ {X Y}     → LG X ⊢ Y ⁰ → LG Y ⊢ ₀ X
  r₀⁰ : ∀ {X Y}     → LG Y ⊢ ₀ X → LG X ⊢ Y ⁰
  r¹₁ : ∀ {X Y}     → LG X ¹ ⊢ Y → LG ₁ Y ⊢ X
  r₁¹ : ∀ {X Y}     → LG ₁ Y ⊢ X → LG X ¹ ⊢ Y

  -- rules for (⇐ , ⊗ , ⇒)
  ⊗ᴸ  : ∀ {Y A B}   → LG · A · ⊗ · B · ⊢ Y → LG · A ⊗ B · ⊢ Y
  ⊗ᴿ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG Y ⊢[ B ] → LG X ⊗ Y ⊢[ A ⊗ B ]
  ⇒ᴸ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG [ A ⇒ B ]⊢ X ⇒ Y
  ⇒ᴿ  : ∀ {X A B}   → LG X ⊢ · A · ⇒ · B · → LG X ⊢ · A ⇒ B ·
  ⇐ᴸ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG [ B ⇐ A ]⊢ Y ⇐ X
  ⇐ᴿ  : ∀ {X A B}   → LG X ⊢ · B · ⇐ · A · → LG X ⊢ · B ⇐ A ·
  r⇒⊗ : ∀ {X Y Z}   → LG Y ⊢ X ⇒ Z → LG X ⊗ Y ⊢ Z
  r⊗⇒ : ∀ {X Y Z}   → LG X ⊗ Y ⊢ Z → LG Y ⊢ X ⇒ Z
  r⇐⊗ : ∀ {X Y Z}   → LG X ⊢ Z ⇐ Y → LG X ⊗ Y ⊢ Z
  r⊗⇐ : ∀ {X Y Z}   → LG X ⊗ Y ⊢ Z → LG X ⊢ Z ⇐ Y

  -- rules for (⇚ , ⊕ , ⇛)
  ⊕ᴸ  : ∀ {X Y A B} → LG [ B ]⊢ Y → LG [ A ]⊢ X → LG [ B ⊕ A ]⊢ Y ⊕ X
  ⊕ᴿ  : ∀ {X A B}   → LG X ⊢ · B · ⊕ · A · → LG X ⊢ · B ⊕ A ·
  ⇚ᴸ  : ∀ {X A B}   → LG · A · ⇚ · B · ⊢ X → LG · A ⇚ B · ⊢ X
  ⇚ᴿ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG X ⇚ Y ⊢[ A ⇚ B ]
  ⇛ᴸ  : ∀ {X A B}   → LG · B · ⇛ · A · ⊢ X → LG · B ⇛ A · ⊢ X
  ⇛ᴿ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG Y ⇛ X ⊢[ B ⇛ A ]
  r⇚⊕ : ∀ {X Y Z}   → LG Z ⇚ X ⊢ Y → LG Z ⊢ Y ⊕ X
  r⊕⇚ : ∀ {X Y Z}   → LG Z ⊢ Y ⊕ X → LG Z ⇚ X ⊢ Y
  r⇛⊕ : ∀ {X Y Z}   → LG Y ⇛ Z ⊢ X → LG Z ⊢ Y ⊕ X
  r⊕⇛ : ∀ {X Y Z}   → LG Z ⊢ Y ⊕ X → LG Y ⇛ Z ⊢ X

  -- grishin interaction principes
  d⇛⇐ : ∀ {X Y Z W} → LG X ⊗ Y ⊢ Z ⊕ W → LG Z ⇛ X ⊢ W ⇐ Y
  d⇛⇒ : ∀ {X Y Z W} → LG X ⊗ Y ⊢ Z ⊕ W → LG Z ⇛ Y ⊢ X ⇒ W
  d⇚⇒ : ∀ {X Y Z W} → LG X ⊗ Y ⊢ Z ⊕ W → LG Y ⇚ W ⊢ X ⇒ Z
  d⇚⇐ : ∀ {X Y Z W} → LG X ⊗ Y ⊢ Z ⊕ W → LG X ⇚ W ⊢ Z ⇐ Y
