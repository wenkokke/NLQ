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


module Logic.Classical.Ordered.LambekGrishin.Base {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type                Atom
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Atom
open import Logic.Classical.Ordered.LambekGrishin.Judgement           Atom


infix 1  LG_

data LG_ : Judgement → Set ℓ where

  -- axioms
  ax⁺ : ∀ {A}       → LG · A · ⊢[ A ]
  ax⁻ : ∀ {B}       → LG [ B ]⊢ · B ·

  -- (de)focus right and left
  ⇁   : ∀ {X B}     → LG X ⊢ · B · → LG X ⊢[ B ]
  ↽   : ∀ {A Y}     → LG · A · ⊢ Y → LG [ A ]⊢ Y
  ⇀   : ∀ {X B}     → LG X ⊢[ B ] → LG X ⊢ · B ·
  ↼   : ∀ {A Y}     → LG [ A ]⊢ Y → LG · A · ⊢ Y

  -- rules for (□ , ◇)
  ◇ᴸ  : ∀ {A Y}     → LG ⟨ · A · ⟩ ⊢ Y → LG · ◇ A · ⊢ Y
  ◇ᴿ  : ∀ {X B}     → LG X ⊢[ B ] → LG ⟨ X ⟩ ⊢[ ◇ B ]
  □ᴸ  : ∀ {A Y}     → LG [ A ]⊢ Y → LG [ □ A ]⊢ [ Y ]
  □ᴿ  : ∀ {X B}     → LG X ⊢ [ · B · ] → LG X ⊢ · □ B ·
  r□◇ : ∀ {X Y}     → LG X ⊢ [ Y ] → LG ⟨ X ⟩ ⊢ Y
  r◇□ : ∀ {X Y}     → LG ⟨ X ⟩ ⊢ Y → LG X ⊢ [ Y ]

  --  rules for (₀ , ⁰ , ₁ , ¹)
  ₀ᴸ  : ∀ {A Y}     → LG Y ⊢[ A ] → LG [ ₀ A ]⊢ ₀ Y
  ₀ᴿ  : ∀ {X B}     → LG X ⊢ ₀ · B · → LG X ⊢ · ₀ B ·
  ⁰ᴸ  : ∀ {A Y}     → LG Y ⊢[ A ] → LG [ A ⁰ ]⊢ Y ⁰
  ⁰ᴿ  : ∀ {X B}     → LG X ⊢ · B · ⁰ → LG X ⊢ · B ⁰ ·
  ₁ᴸ  : ∀ {A Y}     → LG ₁ · A · ⊢ Y → LG · ₁ A · ⊢ Y
  ₁ᴿ  : ∀ {X B}     → LG [ B ]⊢ X → LG ₁ X ⊢[ ₁ B ]
  ¹ᴸ  : ∀ {A Y}     → LG · A · ¹ ⊢ Y → LG · A ¹ · ⊢ Y
  ¹ᴿ  : ∀ {X B}     → LG [ B ]⊢ X → LG X ¹ ⊢[ B ¹ ]
  r⁰₀ : ∀ {X Y}     → LG Y ⊢ X ⁰ → LG X ⊢ ₀ Y
  r₀⁰ : ∀ {X Y}     → LG Y ⊢ ₀ X → LG X ⊢ Y ⁰
  r¹₁ : ∀ {X Y}     → LG Y ¹ ⊢ X → LG ₁ X ⊢ Y
  r₁¹ : ∀ {X Y}     → LG ₁ Y ⊢ X → LG X ¹ ⊢ Y

  -- rules for (⇐ , ⊗ , ⇒)
  ⊗ᴸ  : ∀ {A B Y}   → LG · A · ⊗ · B · ⊢ Y → LG · A ⊗ B · ⊢ Y
  ⊗ᴿ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG Y ⊢[ B ] → LG X ⊗ Y ⊢[ A ⊗ B ]
  ⇒ᴸ  : ∀ {A B X Y} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG [ A ⇒ B ]⊢ X ⇒ Y
  ⇒ᴿ  : ∀ {X A B}   → LG X ⊢ · A · ⇒ · B · → LG X ⊢ · A ⇒ B ·
  ⇐ᴸ  : ∀ {B A Y X} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG [ B ⇐ A ]⊢ Y ⇐ X
  ⇐ᴿ  : ∀ {X B A}   → LG X ⊢ · B · ⇐ · A · → LG X ⊢ · B ⇐ A ·
  r⇒⊗ : ∀ {X Y Z}   → LG Y ⊢ X ⇒ Z → LG X ⊗ Y ⊢ Z
  r⊗⇒ : ∀ {Y X Z}   → LG X ⊗ Y ⊢ Z → LG Y ⊢ X ⇒ Z
  r⇐⊗ : ∀ {X Y Z}   → LG X ⊢ Z ⇐ Y → LG X ⊗ Y ⊢ Z
  r⊗⇐ : ∀ {X Z Y}   → LG X ⊗ Y ⊢ Z → LG X ⊢ Z ⇐ Y

  -- rules for (⇚ , ⊕ , ⇛)
  ⊕ᴸ  : ∀ {B A Y X} → LG [ B ]⊢ Y → LG [ A ]⊢ X → LG [ B ⊕ A ]⊢ Y ⊕ X
  ⊕ᴿ  : ∀ {X B A}   → LG X ⊢ · B · ⊕ · A · → LG X ⊢ · B ⊕ A ·
  ⇚ᴸ  : ∀ {A B X}   → LG · A · ⇚ · B · ⊢ X → LG · A ⇚ B · ⊢ X
  ⇚ᴿ  : ∀ {X Y A B} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG X ⇚ Y ⊢[ A ⇚ B ]
  ⇛ᴸ  : ∀ {B A X}   → LG · B · ⇛ · A · ⊢ X → LG · B ⇛ A · ⊢ X
  ⇛ᴿ  : ∀ {Y X B A} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG Y ⇛ X ⊢[ B ⇛ A ]
  r⇚⊕ : ∀ {Z Y X}   → LG Z ⇚ X ⊢ Y → LG Z ⊢ Y ⊕ X
  r⊕⇚ : ∀ {Z X Y}   → LG Z ⊢ Y ⊕ X → LG Z ⇚ X ⊢ Y
  r⇛⊕ : ∀ {Z Y X}   → LG Y ⇛ Z ⊢ X → LG Z ⊢ Y ⊕ X
  r⊕⇛ : ∀ {Y Z X}   → LG Z ⊢ Y ⊕ X → LG Y ⇛ Z ⊢ X

  -- grishin interaction principes
  d⇛⇐ : ∀ {Z X W Y} → LG X ⊗ Y ⊢ Z ⊕ W → LG Z ⇛ X ⊢ W ⇐ Y
  d⇛⇒ : ∀ {Z Y X W} → LG X ⊗ Y ⊢ Z ⊕ W → LG Z ⇛ Y ⊢ X ⇒ W
  d⇚⇒ : ∀ {Y W X Z} → LG X ⊗ Y ⊢ Z ⊕ W → LG Y ⇚ W ⊢ X ⇒ Z
  d⇚⇐ : ∀ {X W Z Y} → LG X ⊗ Y ⊢ Z ⊕ W → LG X ⇚ W ⊢ Z ⇐ Y



-- raising and lowering
↑₀′ : ∀ {A} → LG · A · ⊢ · ₀ (A ⁰) ·
↑₀′ = ₀ᴿ (r⁰₀ (↼ (⁰ᴸ ax⁺)))
↑⁰′ : ∀ {A} → LG · A · ⊢ · (₀ A) ⁰ ·
↑⁰′ = ⁰ᴿ (r₀⁰ (↼ (₀ᴸ ax⁺)))
↓₁′ : ∀ {A} → LG · ₁ (A ¹) · ⊢ · A ·
↓₁′ = ₁ᴸ (r¹₁ (⇀ (¹ᴿ ax⁻)))
↓¹′ : ∀ {A} → LG · (₁ A) ¹ · ⊢ · A ·
↓¹′ = ¹ᴸ (r₁¹ (⇀ (₁ᴿ ax⁻)))


-- monotonicity
m⁰′ : ∀ {A B} → LG · B · ⊢ · A · → LG ·  A ⁰ · ⊢ · B ⁰ ·
m⁰′ f = ⁰ᴿ (↼ (⁰ᴸ (⇁ f)))
m₀′ : ∀ {A B} → LG · B · ⊢ · A · → LG · ₀ A  · ⊢ · ₀ B   ·
m₀′ f = ₀ᴿ (↼ (₀ᴸ (⇁ f)))
m₁′ : ∀ {A B} → LG · B · ⊢ · A · → LG · ₁ A  · ⊢ · ₁ B ·
m₁′ f = ₁ᴸ (⇀ (₁ᴿ (↽ f)))
m¹′ : ∀ {A B} → LG · B · ⊢ · A · → LG ·  A ¹ · ⊢ · B ¹ ·
m¹′ f = ¹ᴸ (⇀ (¹ᴿ (↽ f)))

-- symmetries that hold
_⋈ᵗ : ∀ {J} → LG J → LG J ⋈ᴶ
ax⁺     ⋈ᵗ = ax⁺
ax⁻     ⋈ᵗ = ax⁻
⇁   f   ⋈ᵗ = ⇁ (f ⋈ᵗ)
↽   f   ⋈ᵗ = ↽ (f ⋈ᵗ)
⇀   f   ⋈ᵗ = ⇀ (f ⋈ᵗ)
↼   f   ⋈ᵗ = ↼ (f ⋈ᵗ)
◇ᴸ  f   ⋈ᵗ = ◇ᴸ (f ⋈ᵗ)
◇ᴿ  f   ⋈ᵗ = ◇ᴿ (f ⋈ᵗ)
□ᴸ  f   ⋈ᵗ = □ᴸ (f ⋈ᵗ)
□ᴿ  f   ⋈ᵗ = □ᴿ (f ⋈ᵗ)
r□◇ f   ⋈ᵗ = r□◇ (f ⋈ᵗ)
r◇□ f   ⋈ᵗ = r◇□ (f ⋈ᵗ)
₀ᴸ  f   ⋈ᵗ = ⁰ᴸ (f ⋈ᵗ)
₀ᴿ  f   ⋈ᵗ = ⁰ᴿ (f ⋈ᵗ)
⁰ᴸ  f   ⋈ᵗ = ₀ᴸ (f ⋈ᵗ)
⁰ᴿ  f   ⋈ᵗ = ₀ᴿ (f ⋈ᵗ)
₁ᴸ  f   ⋈ᵗ = ¹ᴸ (f ⋈ᵗ)
₁ᴿ  f   ⋈ᵗ = ¹ᴿ (f ⋈ᵗ)
¹ᴸ  f   ⋈ᵗ = ₁ᴸ (f ⋈ᵗ)
¹ᴿ  f   ⋈ᵗ = ₁ᴿ (f ⋈ᵗ)
r⁰₀ f   ⋈ᵗ = r₀⁰ (f ⋈ᵗ)
r₀⁰ f   ⋈ᵗ = r⁰₀ (f ⋈ᵗ)
r¹₁ f   ⋈ᵗ = r₁¹ (f ⋈ᵗ)
r₁¹ f   ⋈ᵗ = r¹₁ (f ⋈ᵗ)
⊗ᴸ  f   ⋈ᵗ = ⊗ᴸ (f ⋈ᵗ)
⊗ᴿ  f g ⋈ᵗ = ⊗ᴿ (g ⋈ᵗ) (f ⋈ᵗ)
⇒ᴸ  f g ⋈ᵗ = ⇐ᴸ (f ⋈ᵗ) (g ⋈ᵗ)
⇒ᴿ  f   ⋈ᵗ = ⇐ᴿ (f ⋈ᵗ)
⇐ᴸ  f g ⋈ᵗ = ⇒ᴸ (f ⋈ᵗ) (g ⋈ᵗ)
⇐ᴿ  f   ⋈ᵗ = ⇒ᴿ (f ⋈ᵗ)
r⇒⊗ f   ⋈ᵗ = r⇐⊗ (f ⋈ᵗ)
r⊗⇒ f   ⋈ᵗ = r⊗⇐ (f ⋈ᵗ)
r⇐⊗ f   ⋈ᵗ = r⇒⊗ (f ⋈ᵗ)
r⊗⇐ f   ⋈ᵗ = r⊗⇒ (f ⋈ᵗ)
⊕ᴸ  f g ⋈ᵗ = ⊕ᴸ (g ⋈ᵗ) (f ⋈ᵗ)
⊕ᴿ  f   ⋈ᵗ = ⊕ᴿ (f ⋈ᵗ)
⇚ᴸ  f   ⋈ᵗ = ⇛ᴸ (f ⋈ᵗ)
⇚ᴿ  f g ⋈ᵗ = ⇛ᴿ (f ⋈ᵗ) (g ⋈ᵗ)
⇛ᴸ  f   ⋈ᵗ = ⇚ᴸ (f ⋈ᵗ)
⇛ᴿ  f g ⋈ᵗ = ⇚ᴿ (f ⋈ᵗ) (g ⋈ᵗ)
r⇚⊕ f   ⋈ᵗ = r⇛⊕ (f ⋈ᵗ)
r⊕⇚ f   ⋈ᵗ = r⊕⇛ (f ⋈ᵗ)
r⇛⊕ f   ⋈ᵗ = r⇚⊕ (f ⋈ᵗ)
r⊕⇛ f   ⋈ᵗ = r⊕⇚ (f ⋈ᵗ)
d⇛⇐ f   ⋈ᵗ = d⇚⇒ (f ⋈ᵗ)
d⇛⇒ f   ⋈ᵗ = d⇚⇐ (f ⋈ᵗ)
d⇚⇒ f   ⋈ᵗ = d⇛⇐ (f ⋈ᵗ)
d⇚⇐ f   ⋈ᵗ = d⇛⇒ (f ⋈ᵗ)

_∞ᵗ : ∀ {J} → LG J → LG J ∞ᴶ
ax⁺     ∞ᵗ = ax⁻
ax⁻     ∞ᵗ = ax⁺
⇁   f   ∞ᵗ = ↽ (f ∞ᵗ)
↽   f   ∞ᵗ = ⇁ (f ∞ᵗ)
⇀   f   ∞ᵗ = ↼ (f ∞ᵗ)
↼   f   ∞ᵗ = ⇀ (f ∞ᵗ)
◇ᴸ  f   ∞ᵗ = □ᴿ (f ∞ᵗ)
◇ᴿ  f   ∞ᵗ = □ᴸ (f ∞ᵗ)
□ᴸ  f   ∞ᵗ = ◇ᴿ (f ∞ᵗ)
□ᴿ  f   ∞ᵗ = ◇ᴸ (f ∞ᵗ)
r□◇ f   ∞ᵗ = r◇□ (f ∞ᵗ)
r◇□ f   ∞ᵗ = r□◇ (f ∞ᵗ)
₀ᴸ  f   ∞ᵗ = ¹ᴿ (f ∞ᵗ)
₀ᴿ  f   ∞ᵗ = ¹ᴸ (f ∞ᵗ)
⁰ᴸ  f   ∞ᵗ = ₁ᴿ (f ∞ᵗ)
⁰ᴿ  f   ∞ᵗ = ₁ᴸ (f ∞ᵗ)
₁ᴸ  f   ∞ᵗ = ⁰ᴿ (f ∞ᵗ)
₁ᴿ  f   ∞ᵗ = ⁰ᴸ (f ∞ᵗ)
¹ᴸ  f   ∞ᵗ = ₀ᴿ (f ∞ᵗ)
¹ᴿ  f   ∞ᵗ = ₀ᴸ (f ∞ᵗ)
r⁰₀ f   ∞ᵗ = r₁¹ (f ∞ᵗ)
r₀⁰ f   ∞ᵗ = r¹₁ (f ∞ᵗ)
r¹₁ f   ∞ᵗ = r₀⁰ (f ∞ᵗ)
r₁¹ f   ∞ᵗ = r⁰₀ (f ∞ᵗ)
⊗ᴸ  f   ∞ᵗ = ⊕ᴿ (f ∞ᵗ)
⊗ᴿ  f g ∞ᵗ = ⊕ᴸ (g ∞ᵗ) (f ∞ᵗ)
⇒ᴸ  f g ∞ᵗ = ⇚ᴿ (g ∞ᵗ) (f ∞ᵗ)
⇒ᴿ  f   ∞ᵗ = ⇚ᴸ (f ∞ᵗ)
⇐ᴸ  f g ∞ᵗ = ⇛ᴿ (g ∞ᵗ) (f ∞ᵗ)
⇐ᴿ  f   ∞ᵗ = ⇛ᴸ (f ∞ᵗ)
r⇒⊗ f   ∞ᵗ = r⇚⊕ (f ∞ᵗ)
r⊗⇒ f   ∞ᵗ = r⊕⇚ (f ∞ᵗ)
r⇐⊗ f   ∞ᵗ = r⇛⊕ (f ∞ᵗ)
r⊗⇐ f   ∞ᵗ = r⊕⇛ (f ∞ᵗ)
⊕ᴸ  f g ∞ᵗ = ⊗ᴿ (g ∞ᵗ) (f ∞ᵗ)
⊕ᴿ  f   ∞ᵗ = ⊗ᴸ (f ∞ᵗ)
⇚ᴸ  f   ∞ᵗ = ⇒ᴿ (f ∞ᵗ)
⇚ᴿ  f g ∞ᵗ = ⇒ᴸ (g ∞ᵗ) (f ∞ᵗ)
⇛ᴸ  f   ∞ᵗ = ⇐ᴿ (f ∞ᵗ)
⇛ᴿ  f g ∞ᵗ = ⇐ᴸ (g ∞ᵗ) (f ∞ᵗ)
r⇚⊕ f   ∞ᵗ = r⇒⊗ (f ∞ᵗ)
r⊕⇚ f   ∞ᵗ = r⊗⇒ (f ∞ᵗ)
r⇛⊕ f   ∞ᵗ = r⇐⊗ (f ∞ᵗ)
r⊕⇛ f   ∞ᵗ = r⊗⇐ (f ∞ᵗ)
d⇛⇐ f   ∞ᵗ = d⇛⇐ (f ∞ᵗ)
d⇛⇒ f   ∞ᵗ = d⇚⇐ (f ∞ᵗ)
d⇚⇒ f   ∞ᵗ = d⇚⇒ (f ∞ᵗ)
d⇚⇐ f   ∞ᵗ = d⇛⇒ (f ∞ᵗ)
