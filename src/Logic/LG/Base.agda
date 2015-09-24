------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Function using (_∘_)


module Logic.LG.Base {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom
open import Logic.LG.Sequent             Atom


-- Why are `⇀` and `↼` included?
--
--   While the defocussing rules (⇀ , ↼) can be derived using cut,
--   the suggested procedure for "cut elimination" leaves some cuts in
--   the derivation---namely, those cuts with axiomatic premises. This
--   means that we, in effect, take an axiomatisation where we have the
--   rule `cut` instead of `⇀` and `↼`, but restrict it to only allow
--   for axiomatic premises (i.e. `cut ax⁺ _` and `cut _ ax⁻`)... which
--   in reality is the same axiomatisation, but more cumbersome.


infix 2 LG_ _⊢LG_ [_]⊢LG_ _⊢LG[_]


mutual
  _⊢LG_ : Structure + → Structure - → Set ℓ
  X ⊢LG Y = LG X ⊢ Y

  _⊢LG[_] : Structure + → Type → Set ℓ
  X ⊢LG[ B ] = LG X ⊢[ B ]

  [_]⊢LG_ : Type → Structure - → Set ℓ
  [ A ]⊢LG Y = LG [ A ]⊢ Y

  data LG_ : Sequent → Set ℓ where

    ax⁺ : ∀ {A} → · A · ⊢LG[ A ]
    ax⁻ : ∀ {A} → [ A ]⊢LG · A ·

    ⇁   : ∀ {A X} → X ⊢LG · A · → X ⊢LG[  A  ]
    ↽   : ∀ {A X} →  · A · ⊢LG X → [  A  ]⊢LG X
    ⇀   : ∀ {A X} → X ⊢LG[  A  ] → X ⊢LG · A ·
    ↼   : ∀ {A X} → [  A  ]⊢LG X →  · A · ⊢LG X

    ◇L  : ∀ {Y A}     →  ⟨ · A · ⟩ ⊢LG Y → · ◇ A · ⊢LG Y
    ◇R  : ∀ {X B}     →  X ⊢LG[ B ] → ⟨ X ⟩ ⊢LG[ ◇ B ]
    □L  : ∀ {A Y}     →  [ A ]⊢LG Y → [ □ A ]⊢LG [ Y ]
    □R  : ∀ {X A}     →  X ⊢LG [ · A · ] → X ⊢LG · □ A ·
    r□◇ : ∀ {X Y}     →  X ⊢LG [ Y ] → ⟨ X ⟩ ⊢LG Y
    r◇□ : ∀ {X Y}     →  ⟨ X ⟩ ⊢LG Y → X ⊢LG [ Y ]

    ₀L  : ∀ {X A}     →  X ⊢LG[ A ] → [ ₀ A ]⊢LG ₀ X
    ₀R  : ∀ {X A}     →  X ⊢LG ₀ · A · → X ⊢LG · ₀ A ·
    ⁰L  : ∀ {X A}     →  X ⊢LG[ A ] → [ A ⁰ ]⊢LG X ⁰
    ⁰R  : ∀ {X A}     →  X ⊢LG · A · ⁰ → X ⊢LG · A ⁰ ·
    ₁L  : ∀ {Y A}     →  ₁ · A · ⊢LG Y → · ₁ A · ⊢LG Y
    ₁R  : ∀ {Y A}     →  [ A ]⊢LG Y → ₁ Y ⊢LG[ ₁ A ]
    ¹L  : ∀ {Y A}     →  · A · ¹ ⊢LG Y → · A ¹ · ⊢LG Y
    ¹R  : ∀ {Y A}     →  [ A ]⊢LG Y → Y ¹ ⊢LG[ A ¹ ]
    r⁰₀ : ∀ {X Y}     →  X ⊢LG Y ⁰ → Y ⊢LG ₀ X
    r₀⁰ : ∀ {X Y}     →  Y ⊢LG ₀ X → X ⊢LG Y ⁰
    r¹₁ : ∀ {X Y}     →  X ¹ ⊢LG Y → ₁ Y ⊢LG X
    r₁¹ : ∀ {X Y}     →  ₁ Y ⊢LG X → X ¹ ⊢LG Y

    ⊗L  : ∀ {Y A B}   →  · A · ⊗ · B · ⊢LG Y → · A ⊗ B · ⊢LG Y
    ⊗R  : ∀ {X Y A B} →  X ⊢LG[ A ] → Y ⊢LG[ B ] → X ⊗ Y ⊢LG[ A ⊗ B ]
    ⇒L  : ∀ {X Y A B} →  X ⊢LG[ A ] → [ B ]⊢LG Y → [ A ⇒ B ]⊢LG X ⇒ Y
    ⇒R  : ∀ {X A B}   →  X ⊢LG · A · ⇒ · B · → X ⊢LG · A ⇒ B ·
    ⇐L  : ∀ {X Y A B} →  X ⊢LG[ A ] → [ B ]⊢LG Y → [ B ⇐ A ]⊢LG Y ⇐ X
    ⇐R  : ∀ {X A B}   →  X ⊢LG · B · ⇐ · A · → X ⊢LG · B ⇐ A ·
    r⇒⊗ : ∀ {X Y Z}   →  Y ⊢LG X ⇒ Z → X ⊗ Y ⊢LG Z
    r⊗⇒ : ∀ {X Y Z}   →  X ⊗ Y ⊢LG Z → Y ⊢LG X ⇒ Z
    r⇐⊗ : ∀ {X Y Z}   →  X ⊢LG Z ⇐ Y → X ⊗ Y ⊢LG Z
    r⊗⇐ : ∀ {X Y Z}   →  X ⊗ Y ⊢LG Z → X ⊢LG Z ⇐ Y

    ⊕L   : ∀ {X Y A B} →  [ B ]⊢LG Y →  [ A ]⊢LG X →  [ B ⊕ A ]⊢LG Y ⊕ X
    ⊕R   : ∀ {X A B}   →  X ⊢LG · B · ⊕ · A · →  X ⊢LG · B ⊕ A ·
    ⇚L   : ∀ {X A B}   →  · A · ⇚ · B · ⊢LG X →  · A ⇚ B · ⊢LG X
    ⇚R   : ∀ {X Y A B} →  X ⊢LG[ A ] →  [ B ]⊢LG Y →  X ⇚ Y ⊢LG[ A ⇚ B ]
    ⇛L   : ∀ {X A B}   →  · B · ⇛ · A · ⊢LG X →  · B ⇛ A · ⊢LG X
    ⇛R   : ∀ {X Y A B} →  X ⊢LG[ A ] →  [ B ]⊢LG Y →  Y ⇛ X ⊢LG[ B ⇛ A ]
    r⇚⊕  : ∀ {X Y Z}   →  Z ⇚ X ⊢LG Y →  Z ⊢LG Y ⊕ X
    r⊕⇚  : ∀ {X Y Z}   →  Z ⊢LG Y ⊕ X →  Z ⇚ X ⊢LG Y
    r⇛⊕  : ∀ {X Y Z}   →  Y ⇛ Z ⊢LG X →  Z ⊢LG Y ⊕ X
    r⊕⇛  : ∀ {X Y Z}   →  Z ⊢LG Y ⊕ X →  Y ⇛ Z ⊢LG X

    d⇛⇐  : ∀ {X Y Z W} →  X ⊗ Y ⊢LG Z ⊕ W →  Z ⇛ X ⊢LG W ⇐ Y
    d⇛⇒  : ∀ {X Y Z W} →  X ⊗ Y ⊢LG Z ⊕ W →  Z ⇛ Y ⊢LG X ⇒ W
    d⇚⇒  : ∀ {X Y Z W} →  X ⊗ Y ⊢LG Z ⊕ W →  Y ⇚ W ⊢LG X ⇒ Z
    d⇚⇐  : ∀ {X Y Z W} →  X ⊗ Y ⊢LG Z ⊕ W →  X ⇚ W ⊢LG Z ⇐ Y



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
