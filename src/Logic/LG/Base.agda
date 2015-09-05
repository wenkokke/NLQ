------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)


module Logic.LG.Base {ℓ} (Atom : Set ℓ) where


open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Sequent           Atom


-- Why are `⇀` and `↼` included?
--
--   While the defocussing rules (⇀ , ↼) can be derived using cut,
--   the suggested procedure for "cut elimination" leaves some cuts in
--   the derivation---namely, those cuts with axiomatic premises. This
--   means that we, in effect, take an axiomatisation where we have the
--   rule `cut` instead of `⇀` and `↼`, but restrict it to only allow
--   for axiomatic premises (i.e. `cut ax⁺ _` and `cut _ ax⁻`)... which
--   in reality is the same axiomatisation, but more cumbersome.


infix 1  LG_

data LG_ : Sequent → Set ℓ where

  -- axioms
  ax⁺ : ∀ {A}       → LG · A · ⊢[ A ]
  ax⁻ : ∀ {B}       → LG [ B ]⊢ · B ·

  -- (de)focus right and left
  ⇁   : ∀ {X B}     → LG X ⊢ · B · → LG X ⊢[ B ]
  ↽   : ∀ {A Y}     → LG · A · ⊢ Y → LG [ A ]⊢ Y
  ⇀   : ∀ {X B}     → LG X ⊢[ B ] → LG X ⊢ · B ·
  ↼   : ∀ {A Y}     → LG [ A ]⊢ Y → LG · A · ⊢ Y

  -- rules for (□ , ◇)
  ◇L  : ∀ {A Y}     → LG ⟨ · A · ⟩ ⊢ Y → LG · ◇ A · ⊢ Y
  ◇R  : ∀ {X B}     → LG X ⊢[ B ] → LG ⟨ X ⟩ ⊢[ ◇ B ]
  □L  : ∀ {A Y}     → LG [ A ]⊢ Y → LG [ □ A ]⊢ [ Y ]
  □R  : ∀ {X B}     → LG X ⊢ [ · B · ] → LG X ⊢ · □ B ·
  r□◇ : ∀ {X Y}     → LG X ⊢ [ Y ] → LG ⟨ X ⟩ ⊢ Y
  r◇□ : ∀ {X Y}     → LG ⟨ X ⟩ ⊢ Y → LG X ⊢ [ Y ]

  --  rules for (₀ , ⁰ , ₁ , ¹)
  ₀L  : ∀ {A Y}     → LG Y ⊢[ A ] → LG [ ₀ A ]⊢ ₀ Y
  ₀R  : ∀ {X B}     → LG X ⊢ ₀ · B · → LG X ⊢ · ₀ B ·
  ⁰L  : ∀ {A Y}     → LG Y ⊢[ A ] → LG [ A ⁰ ]⊢ Y ⁰
  ⁰R  : ∀ {X B}     → LG X ⊢ · B · ⁰ → LG X ⊢ · B ⁰ ·
  ₁L  : ∀ {A Y}     → LG ₁ · A · ⊢ Y → LG · ₁ A · ⊢ Y
  ₁R  : ∀ {X B}     → LG [ B ]⊢ X → LG ₁ X ⊢[ ₁ B ]
  ¹L  : ∀ {A Y}     → LG · A · ¹ ⊢ Y → LG · A ¹ · ⊢ Y
  ¹R  : ∀ {X B}     → LG [ B ]⊢ X → LG X ¹ ⊢[ B ¹ ]
  r⁰₀ : ∀ {X Y}     → LG Y ⊢ X ⁰ → LG X ⊢ ₀ Y
  r₀⁰ : ∀ {X Y}     → LG Y ⊢ ₀ X → LG X ⊢ Y ⁰
  r¹₁ : ∀ {X Y}     → LG Y ¹ ⊢ X → LG ₁ X ⊢ Y
  r₁¹ : ∀ {X Y}     → LG ₁ Y ⊢ X → LG X ¹ ⊢ Y

  -- rules for (⇐ , ⊗ , ⇒)
  ⊗L  : ∀ {A B Y}   → LG · A · ⊗ · B · ⊢ Y → LG · A ⊗ B · ⊢ Y
  ⊗R  : ∀ {X Y A B} → LG X ⊢[ A ] → LG Y ⊢[ B ] → LG X ⊗ Y ⊢[ A ⊗ B ]
  ⇒L  : ∀ {A B X Y} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG [ A ⇒ B ]⊢ X ⇒ Y
  ⇒R  : ∀ {X A B}   → LG X ⊢ · A · ⇒ · B · → LG X ⊢ · A ⇒ B ·
  ⇐L  : ∀ {B A Y X} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG [ B ⇐ A ]⊢ Y ⇐ X
  ⇐R  : ∀ {X B A}   → LG X ⊢ · B · ⇐ · A · → LG X ⊢ · B ⇐ A ·
  r⇒⊗ : ∀ {X Y Z}   → LG Y ⊢ X ⇒ Z → LG X ⊗ Y ⊢ Z
  r⊗⇒ : ∀ {Y X Z}   → LG X ⊗ Y ⊢ Z → LG Y ⊢ X ⇒ Z
  r⇐⊗ : ∀ {X Y Z}   → LG X ⊢ Z ⇐ Y → LG X ⊗ Y ⊢ Z
  r⊗⇐ : ∀ {X Z Y}   → LG X ⊗ Y ⊢ Z → LG X ⊢ Z ⇐ Y

  -- rules for (⇚ , ⊕ , ⇛)
  ⊕L  : ∀ {B A Y X} → LG [ B ]⊢ Y → LG [ A ]⊢ X → LG [ B ⊕ A ]⊢ Y ⊕ X
  ⊕R  : ∀ {X B A}   → LG X ⊢ · B · ⊕ · A · → LG X ⊢ · B ⊕ A ·
  ⇚L  : ∀ {A B X}   → LG · A · ⇚ · B · ⊢ X → LG · A ⇚ B · ⊢ X
  ⇚R  : ∀ {X Y A B} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG X ⇚ Y ⊢[ A ⇚ B ]
  ⇛L  : ∀ {B A X}   → LG · B · ⇛ · A · ⊢ X → LG · B ⇛ A · ⊢ X
  ⇛R  : ∀ {Y X B A} → LG X ⊢[ A ] → LG [ B ]⊢ Y → LG Y ⇛ X ⊢[ B ⇛ A ]
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
↑₀′ = ₀R (r⁰₀ (↼ (⁰L ax⁺)))
↑⁰′ : ∀ {A} → LG · A · ⊢ · (₀ A) ⁰ ·
↑⁰′ = ⁰R (r₀⁰ (↼ (₀L ax⁺)))
↓₁′ : ∀ {A} → LG · ₁ (A ¹) · ⊢ · A ·
↓₁′ = ₁L (r¹₁ (⇀ (¹R ax⁻)))
↓¹′ : ∀ {A} → LG · (₁ A) ¹ · ⊢ · A ·
↓¹′ = ¹L (r₁¹ (⇀ (₁R ax⁻)))


-- monotonicity
m⁰′ : ∀ {A B} → LG · B · ⊢ · A · → LG ·  A ⁰ · ⊢ · B ⁰ ·
m⁰′ f = ⁰R (↼ (⁰L (⇁ f)))
m₀′ : ∀ {A B} → LG · B · ⊢ · A · → LG · ₀ A  · ⊢ · ₀ B   ·
m₀′ f = ₀R (↼ (₀L (⇁ f)))
m₁′ : ∀ {A B} → LG · B · ⊢ · A · → LG · ₁ A  · ⊢ · ₁ B ·
m₁′ f = ₁L (⇀ (₁R (↽ f)))
m¹′ : ∀ {A B} → LG · B · ⊢ · A · → LG ·  A ¹ · ⊢ · B ¹ ·
m¹′ f = ¹L (⇀ (¹R (↽ f)))

-- symmetries that hold
_⋈ᵗ : ∀ {J} → LG J → LG J ⋈ʲ
ax⁺     ⋈ᵗ = ax⁺
ax⁻     ⋈ᵗ = ax⁻
⇁   f   ⋈ᵗ = ⇁ (f ⋈ᵗ)
↽   f   ⋈ᵗ = ↽ (f ⋈ᵗ)
⇀   f   ⋈ᵗ = ⇀ (f ⋈ᵗ)
↼   f   ⋈ᵗ = ↼ (f ⋈ᵗ)
◇L  f   ⋈ᵗ = ◇L (f ⋈ᵗ)
◇R  f   ⋈ᵗ = ◇R (f ⋈ᵗ)
□L  f   ⋈ᵗ = □L (f ⋈ᵗ)
□R  f   ⋈ᵗ = □R (f ⋈ᵗ)
r□◇ f   ⋈ᵗ = r□◇ (f ⋈ᵗ)
r◇□ f   ⋈ᵗ = r◇□ (f ⋈ᵗ)
₀L  f   ⋈ᵗ = ⁰L (f ⋈ᵗ)
₀R  f   ⋈ᵗ = ⁰R (f ⋈ᵗ)
⁰L  f   ⋈ᵗ = ₀L (f ⋈ᵗ)
⁰R  f   ⋈ᵗ = ₀R (f ⋈ᵗ)
₁L  f   ⋈ᵗ = ¹L (f ⋈ᵗ)
₁R  f   ⋈ᵗ = ¹R (f ⋈ᵗ)
¹L  f   ⋈ᵗ = ₁L (f ⋈ᵗ)
¹R  f   ⋈ᵗ = ₁R (f ⋈ᵗ)
r⁰₀ f   ⋈ᵗ = r₀⁰ (f ⋈ᵗ)
r₀⁰ f   ⋈ᵗ = r⁰₀ (f ⋈ᵗ)
r¹₁ f   ⋈ᵗ = r₁¹ (f ⋈ᵗ)
r₁¹ f   ⋈ᵗ = r¹₁ (f ⋈ᵗ)
⊗L  f   ⋈ᵗ = ⊗L (f ⋈ᵗ)
⊗R  f g ⋈ᵗ = ⊗R (g ⋈ᵗ) (f ⋈ᵗ)
⇒L  f g ⋈ᵗ = ⇐L (f ⋈ᵗ) (g ⋈ᵗ)
⇒R  f   ⋈ᵗ = ⇐R (f ⋈ᵗ)
⇐L  f g ⋈ᵗ = ⇒L (f ⋈ᵗ) (g ⋈ᵗ)
⇐R  f   ⋈ᵗ = ⇒R (f ⋈ᵗ)
r⇒⊗ f   ⋈ᵗ = r⇐⊗ (f ⋈ᵗ)
r⊗⇒ f   ⋈ᵗ = r⊗⇐ (f ⋈ᵗ)
r⇐⊗ f   ⋈ᵗ = r⇒⊗ (f ⋈ᵗ)
r⊗⇐ f   ⋈ᵗ = r⊗⇒ (f ⋈ᵗ)
⊕L  f g ⋈ᵗ = ⊕L (g ⋈ᵗ) (f ⋈ᵗ)
⊕R  f   ⋈ᵗ = ⊕R (f ⋈ᵗ)
⇚L  f   ⋈ᵗ = ⇛L (f ⋈ᵗ)
⇚R  f g ⋈ᵗ = ⇛R (f ⋈ᵗ) (g ⋈ᵗ)
⇛L  f   ⋈ᵗ = ⇚L (f ⋈ᵗ)
⇛R  f g ⋈ᵗ = ⇚R (f ⋈ᵗ) (g ⋈ᵗ)
r⇚⊕ f   ⋈ᵗ = r⇛⊕ (f ⋈ᵗ)
r⊕⇚ f   ⋈ᵗ = r⊕⇛ (f ⋈ᵗ)
r⇛⊕ f   ⋈ᵗ = r⇚⊕ (f ⋈ᵗ)
r⊕⇛ f   ⋈ᵗ = r⊕⇚ (f ⋈ᵗ)
d⇛⇐ f   ⋈ᵗ = d⇚⇒ (f ⋈ᵗ)
d⇛⇒ f   ⋈ᵗ = d⇚⇐ (f ⋈ᵗ)
d⇚⇒ f   ⋈ᵗ = d⇛⇐ (f ⋈ᵗ)
d⇚⇐ f   ⋈ᵗ = d⇛⇒ (f ⋈ᵗ)

_∞ᵗ : ∀ {J} → LG J → LG J ∞ʲ
ax⁺     ∞ᵗ = ax⁻
ax⁻     ∞ᵗ = ax⁺
⇁   f   ∞ᵗ = ↽ (f ∞ᵗ)
↽   f   ∞ᵗ = ⇁ (f ∞ᵗ)
⇀   f   ∞ᵗ = ↼ (f ∞ᵗ)
↼   f   ∞ᵗ = ⇀ (f ∞ᵗ)
◇L  f   ∞ᵗ = □R (f ∞ᵗ)
◇R  f   ∞ᵗ = □L (f ∞ᵗ)
□L  f   ∞ᵗ = ◇R (f ∞ᵗ)
□R  f   ∞ᵗ = ◇L (f ∞ᵗ)
r□◇ f   ∞ᵗ = r◇□ (f ∞ᵗ)
r◇□ f   ∞ᵗ = r□◇ (f ∞ᵗ)
₀L  f   ∞ᵗ = ¹R (f ∞ᵗ)
₀R  f   ∞ᵗ = ¹L (f ∞ᵗ)
⁰L  f   ∞ᵗ = ₁R (f ∞ᵗ)
⁰R  f   ∞ᵗ = ₁L (f ∞ᵗ)
₁L  f   ∞ᵗ = ⁰R (f ∞ᵗ)
₁R  f   ∞ᵗ = ⁰L (f ∞ᵗ)
¹L  f   ∞ᵗ = ₀R (f ∞ᵗ)
¹R  f   ∞ᵗ = ₀L (f ∞ᵗ)
r⁰₀ f   ∞ᵗ = r₁¹ (f ∞ᵗ)
r₀⁰ f   ∞ᵗ = r¹₁ (f ∞ᵗ)
r¹₁ f   ∞ᵗ = r₀⁰ (f ∞ᵗ)
r₁¹ f   ∞ᵗ = r⁰₀ (f ∞ᵗ)
⊗L  f   ∞ᵗ = ⊕R (f ∞ᵗ)
⊗R  f g ∞ᵗ = ⊕L (g ∞ᵗ) (f ∞ᵗ)
⇒L  f g ∞ᵗ = ⇚R (g ∞ᵗ) (f ∞ᵗ)
⇒R  f   ∞ᵗ = ⇚L (f ∞ᵗ)
⇐L  f g ∞ᵗ = ⇛R (g ∞ᵗ) (f ∞ᵗ)
⇐R  f   ∞ᵗ = ⇛L (f ∞ᵗ)
r⇒⊗ f   ∞ᵗ = r⇚⊕ (f ∞ᵗ)
r⊗⇒ f   ∞ᵗ = r⊕⇚ (f ∞ᵗ)
r⇐⊗ f   ∞ᵗ = r⇛⊕ (f ∞ᵗ)
r⊗⇐ f   ∞ᵗ = r⊕⇛ (f ∞ᵗ)
⊕L  f g ∞ᵗ = ⊗R (g ∞ᵗ) (f ∞ᵗ)
⊕R  f   ∞ᵗ = ⊗L (f ∞ᵗ)
⇚L  f   ∞ᵗ = ⇒R (f ∞ᵗ)
⇚R  f g ∞ᵗ = ⇒L (g ∞ᵗ) (f ∞ᵗ)
⇛L  f   ∞ᵗ = ⇐R (f ∞ᵗ)
⇛R  f g ∞ᵗ = ⇐L (g ∞ᵗ) (f ∞ᵗ)
r⇚⊕ f   ∞ᵗ = r⇒⊗ (f ∞ᵗ)
r⊕⇚ f   ∞ᵗ = r⊗⇒ (f ∞ᵗ)
r⇛⊕ f   ∞ᵗ = r⇐⊗ (f ∞ᵗ)
r⊕⇛ f   ∞ᵗ = r⊗⇐ (f ∞ᵗ)
d⇛⇐ f   ∞ᵗ = d⇛⇐ (f ∞ᵗ)
d⇛⇒ f   ∞ᵗ = d⇚⇐ (f ∞ᵗ)
d⇚⇒ f   ∞ᵗ = d⇚⇒ (f ∞ᵗ)
d⇚⇐ f   ∞ᵗ = d⇛⇒ (f ∞ᵗ)
