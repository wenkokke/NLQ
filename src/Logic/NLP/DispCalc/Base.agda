--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.NLP.DispCalc.Base {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NLP.DispCalc.Type      Atom
open import Logic.NLP.DispCalc.Structure Atom
open import Logic.NLP.DispCalc.Sequent   Atom


infix 2 NL_ _⊢NL_ [_]⊢NL_ _⊢NL[_]

mutual
  _⊢NL_ : Structure + → Structure - → Set ℓ
  X ⊢NL Y = NL X ⊢ Y

  _⊢NL[_] : Structure + → Type → Set ℓ
  X ⊢NL[ B ] = NL X ⊢[ B ]

  [_]⊢NL_ : Type → Structure - → Set ℓ
  [ A ]⊢NL Y = NL [ A ]⊢ Y

  data NL_ : Sequent → Set ℓ where

    ax⁺ : ∀ {A} → · A · ⊢NL[ A ]
    ax⁻ : ∀ {A} → [ A ]⊢NL · A ·

    ⇁   : ∀ {A X} → X ⊢NL · A · → X ⊢NL[  A  ]
    ↽   : ∀ {A X} →  · A · ⊢NL X → [  A  ]⊢NL X
    ⇀   : ∀ {A X} → X ⊢NL[  A  ] → X ⊢NL · A ·
    ↼   : ∀ {A X} → [  A  ]⊢NL X →  · A · ⊢NL X

    ⇒L  : ∀ {X Y A B} →  X ⊢NL[ A ] → [ B ]⊢NL Y → [ A ⇒ B ]⊢NL X ⇒ Y
    ⇒R  : ∀ {X A B}   →  X ⊢NL · A · ⇒ · B · → X ⊢NL · A ⇒ B ·
    ⇐L  : ∀ {X Y A B} →  X ⊢NL[ A ] → [ B ]⊢NL Y → [ B ⇐ A ]⊢NL Y ⇐ X
    ⇐R  : ∀ {X A B}   →  X ⊢NL · B · ⇐ · A · → X ⊢NL · B ⇐ A ·

    r⇒⊗ : ∀ {X Y Z}   →  Y ⊢NL X ⇒ Z → X ⊗ Y ⊢NL Z
    r⊗⇒ : ∀ {X Y Z}   →  X ⊗ Y ⊢NL Z → Y ⊢NL X ⇒ Z
    r⇐⊗ : ∀ {X Y Z}   →  X ⊢NL Z ⇐ Y → X ⊗ Y ⊢NL Z
    r⊗⇐ : ∀ {X Y Z}   →  X ⊗ Y ⊢NL Z → X ⊢NL Z ⇐ Y

    -- choice
    &L₁ : ∀ {A B C}   → · A · ⊢NL · C · → · A & B · ⊢NL · C ·
    &L₂ : ∀ {A B C}   → · B · ⊢NL · C · → · A & B · ⊢NL · C ·
    &R  : ∀ {A B C}   → · A · ⊢NL · B · → · A · ⊢NL · C · → · A · ⊢NL · B & C ·

    -- structural postulates for infixation
    ◇L  : ∀ {Y A}     →  ◇ · A · ⊢NL Y → · ◇ A · ⊢NL Y
    ◇R  : ∀ {X B}     →  X ⊢NL[ B ] → ◇ X ⊢NL[ ◇ B ]
    □L  : ∀ {A Y}     →  [ A ]⊢NL Y → [ □ A ]⊢NL □ Y
    □R  : ∀ {X A}     →  X ⊢NL □ · A · → X ⊢NL · □ A ·
    r□◇ : ∀ {X Y}     →  X ⊢NL □ Y → ◇ X ⊢NL Y
    r◇□ : ∀ {X Y}     →  ◇ X ⊢NL Y → X ⊢NL □ Y

    iRR : ∀ {X Y Z W} → (X ⊗ Y) ⊗ ◇ Z ⊢NL W → X ⊗ (Y ⊗ ◇ Z) ⊢NL W
    iLR : ∀ {X Y Z W} → (X ⊗ Y) ⊗ ◇ Z ⊢NL W → (X ⊗ ◇ Z) ⊗ Y ⊢NL W
    iLL : ∀ {X Y Z W} → ◇ Z ⊗ (Y ⊗ X) ⊢NL W → (◇ Z ⊗ Y) ⊗ X ⊢NL W
    iRL : ∀ {X Y Z W} → ◇ Z ⊗ (Y ⊗ X) ⊢NL W → Y ⊗ (◇ Z ⊗ X) ⊢NL W

    -- structural postulates for extraction
    ◆L  : ∀ {Y A}     →  ◆ · A · ⊢NL Y → · ◆ A · ⊢NL Y
    ◆R  : ∀ {X B}     →  X ⊢NL[ B ] → ◆ X ⊢NL[ ◆ B ]
    ■L  : ∀ {A Y}     →  [ A ]⊢NL Y → [ ■ A ]⊢NL ■ Y
    ■R  : ∀ {X A}     →  X ⊢NL ■ · A · → X ⊢NL · ■ A ·
    r■◆ : ∀ {X Y}     →  X ⊢NL ■ Y → ◆ X ⊢NL Y
    r◆■ : ∀ {X Y}     →  ◆ X ⊢NL Y → X ⊢NL ■ Y

    eRR : ∀ {X Y Z W} → X ⊗ (Y ⊗ ◆ Z) ⊢NL W → (X ⊗ Y) ⊗ ◆ Z ⊢NL W
    eLR : ∀ {X Y Z W} → (X ⊗ ◆ Z) ⊗ Y ⊢NL W → (X ⊗ Y) ⊗ ◆ Z ⊢NL W
    eLL : ∀ {X Y Z W} → (◆ Z ⊗ Y) ⊗ X ⊢NL W → ◆ Z ⊗ (Y ⊗ X) ⊢NL W
    eRL : ∀ {X Y Z W} → Y ⊗ (◆ Z ⊗ X) ⊢NL W → ◆ Z ⊗ (Y ⊗ X) ⊢NL W

    -- structural postulates for quantifier raising
    ⬗L  : ∀ {Y A}     →  ⬗ · A · ⊢NL Y → · ⬗ A · ⊢NL Y
    ⬗R  : ∀ {X B}     →  X ⊢NL[ B ] → ⬗ X ⊢NL[ ⬗ B ]
    ◨L  : ∀ {A Y}     →  [ A ]⊢NL Y → [ ◨ A ]⊢NL ◨ Y
    ◨R  : ∀ {X A}     →  X ⊢NL ◨ · A · → X ⊢NL · ◨ A ·
    r◨⬗ : ∀ {X Y}     →  X ⊢NL ◨ Y → ⬗ X ⊢NL Y
    r⬗◨ : ∀ {X Y}     →  ⬗ X ⊢NL Y → X ⊢NL ◨ Y

    ↓RR : ∀ {X Y Z W} → (X ⊗ (Y ⊗ R)) ⊗ ⬗ Z ⊢NL W → X ⊗ (Y ⊗ ⬗ Z) ⊢NL W
    ↓LR : ∀ {X Y Z W} → ((X ⊗ R) ⊗ Y) ⊗ ⬗ Z ⊢NL W → (X ⊗ ⬗ Z) ⊗ Y ⊢NL W
    ↓LL : ∀ {X Y Z W} → ⬗ Z ⊗ ((L ⊗ Y) ⊗ X) ⊢NL W → (⬗ Z ⊗ Y) ⊗ X ⊢NL W
    ↓RL : ∀ {X Y Z W} → ⬗ Z ⊗ (Y ⊗ (L ⊗ X)) ⊢NL W → Y ⊗ (⬗ Z ⊗ X) ⊢NL W

    ⬖L  : ∀ {Y A}     →  ⬖ · A · ⊢NL Y → · ⬖ A · ⊢NL Y
    ⬖R  : ∀ {X B}     →  X ⊢NL[ B ] → ⬖ X ⊢NL[ ⬖ B ]
    ◧L  : ∀ {A Y}     →  [ A ]⊢NL Y → [ ◧ A ]⊢NL ◧ Y
    ◧R  : ∀ {X A}     →  X ⊢NL ◧ · A · → X ⊢NL · ◧ A ·
    r◧⬖ : ∀ {X Y}     →  X ⊢NL ◧ Y → ⬖ X ⊢NL Y
    r⬖◧ : ∀ {X Y}     →  ⬖ X ⊢NL Y → X ⊢NL ◧ Y

    ↑RR : ∀ {X Y Z W} → X ⊗ (Y ⊗ ⬖ Z) ⊢NL W → (X ⊗ (Y ⊗ R)) ⊗ ⬖ Z ⊢NL W
    ↑LR : ∀ {X Y Z W} → (X ⊗ ⬖ Z) ⊗ Y ⊢NL W → ((X ⊗ R) ⊗ Y) ⊗ ⬖ Z ⊢NL W
    ↑LL : ∀ {X Y Z W} → (⬖ Z ⊗ Y) ⊗ X ⊢NL W → ⬖ Z ⊗ ((L ⊗ Y) ⊗ X) ⊢NL W
    ↑RL : ∀ {X Y Z W} → Y ⊗ (⬖ Z ⊗ X) ⊢NL W → ⬖ Z ⊗ (Y ⊗ (L ⊗ X)) ⊢NL W

    -- scope islands
    ⟨⟩R : ∀ {X B}     →  X ⊢NL[ B ] → ⟨ X ⟩ ⊢NL[ ⟨ B ⟩ ]


_⋈ : ∀ {J} → NL J → NL J ⋈ʲ
ax⁺     ⋈ = ax⁺             ; ax⁻     ⋈ = ax⁻
⇁   f   ⋈ = ⇁   (f ⋈)       ; ↽   f   ⋈ = ↽   (f ⋈)
⇀   f   ⋈ = ⇀   (f ⋈)       ; ↼   f   ⋈ = ↼   (f ⋈)
⇒L  f g ⋈ = ⇐L  (f ⋈) (g ⋈) ; ⇒R  f   ⋈ = ⇐R  (f ⋈)
⇐L  f g ⋈ = ⇒L  (f ⋈) (g ⋈) ; ⇐R  f   ⋈ = ⇒R  (f ⋈)
r⇒⊗ f   ⋈ = r⇐⊗ (f ⋈)       ; r⊗⇒ f   ⋈ = r⊗⇐ (f ⋈)
r⇐⊗ f   ⋈ = r⇒⊗ (f ⋈)       ; r⊗⇐ f   ⋈ = r⊗⇒ (f ⋈)
&L₁ f   ⋈ = &L₁ (f ⋈)       ; &L₂ f   ⋈ = &L₂ (f ⋈)
&R  f g ⋈ = &R  (f ⋈) (g ⋈) ; ⟨⟩R f   ⋈ = ⟨⟩R (f ⋈)
◇L  f   ⋈ = ◇L  (f ⋈)       ; ◇R  f   ⋈ = ◇R  (f ⋈)
□L  f   ⋈ = □L  (f ⋈)       ; □R  f   ⋈ = □R  (f ⋈)
r□◇ f   ⋈ = r□◇ (f ⋈)       ; r◇□ f   ⋈ = r◇□ (f ⋈)
iRR f   ⋈ = iLL (f ⋈)       ; iLR f   ⋈ = iRL (f ⋈)
iLL f   ⋈ = iRR (f ⋈)       ; iRL f   ⋈ = iLR (f ⋈)
◆L  f   ⋈ = ◆L  (f ⋈)       ; ◆R  f   ⋈ = ◆R  (f ⋈)
■L  f   ⋈ = ■L  (f ⋈)       ; ■R  f   ⋈ = ■R  (f ⋈)
r■◆ f   ⋈ = r■◆ (f ⋈)       ; r◆■ f   ⋈ = r◆■ (f ⋈)
eRR f   ⋈ = eLL (f ⋈)       ; eLR f   ⋈ = eRL (f ⋈)
eLL f   ⋈ = eRR (f ⋈)       ; eRL f   ⋈ = eLR (f ⋈)
⬗L  f   ⋈ = ⬗L  (f ⋈)       ; ⬗R  f   ⋈ = ⬗R  (f ⋈)
◨L  f   ⋈ = ◨L  (f ⋈)       ; ◨R  f   ⋈ = ◨R  (f ⋈)
r◨⬗ f   ⋈ = r◨⬗ (f ⋈)       ; r⬗◨ f   ⋈ = r⬗◨ (f ⋈)
↓RR f   ⋈ = ↓LL (f ⋈)       ; ↓LR f   ⋈ = ↓RL (f ⋈)
↓LL f   ⋈ = ↓RR (f ⋈)       ; ↓RL f   ⋈ = ↓LR (f ⋈)
⬖L  f   ⋈ = ⬖L  (f ⋈)       ; ⬖R  f   ⋈ = ⬖R  (f ⋈)
◧L  f   ⋈ = ◧L  (f ⋈)       ; ◧R  f   ⋈ = ◧R  (f ⋈)
r◧⬖ f   ⋈ = r◧⬖ (f ⋈)       ; r⬖◧ f   ⋈ = r⬖◧ (f ⋈)
↑RR f   ⋈ = ↑LL (f ⋈)       ; ↑LR f   ⋈ = ↑RL (f ⋈)
↑LL f   ⋈ = ↑RR (f ⋈)       ; ↑RL f   ⋈ = ↑LR (f ⋈)


-- Defined rules for extraction
abstract
  _↾_ : Type → Type → Type
  B ↾ A = B ⇐ ◆ ■ A
  _↿_ : Type → Type → Type
  A ↿ B = ◆ ■ A ⇒ B

  exR : ∀ (X : Context + +) {Y A B}
      → X [ Y ⊗ · A · ] ⊢NL · B · → X [ Y ] ⊢NL · B ↾ A ·
  exR X f = ⇐R (r⊗⇐ (r⇒⊗ (◆L (r⊗⇒ (r⇐⊗ (exR′ X f))))))
    where
    exR′ : ∀ (X : Context + +) {Y A Z}
         → X [ Y ⊗ · A · ] ⊢NL Z → X [ Y ] ⊢NL Z ⇐ ◆ · ■ A ·
    exR′ []       f = r⊗⇐ (r⇒⊗ (r■◆ (↼ (■L (↽ (r⊗⇒ f))))))
    exR′ (_ ⊗> X) f = r⊗⇐ (eRR (r⇒⊗ (r⇐⊗ (exR′ X (r⊗⇒ f)))))
    exR′ (X <⊗ _) f = r⊗⇐ (eLR (r⇐⊗ (r⇐⊗ (exR′ X (r⊗⇐ f)))))

  exL : ∀ (X : Context + +) {Y A B}
      → X [ · A · ⊗ Y ] ⊢NL · B · → X [ Y ] ⊢NL · A ↿ B ·
  exL X f = ⇒R (r⊗⇒ (r⇐⊗ (◆L (r⊗⇐ (r⇒⊗ (exL′ X f))))))
    where
    exL′ : ∀ (X : Context + +) {Y A Z}
         → X [ · A · ⊗ Y ] ⊢NL Z → X [ Y ] ⊢NL ◆ · ■ A · ⇒ Z
    exL′ []       f = r⊗⇒ (r⇐⊗ (r■◆ (↼ (■L (↽ (r⊗⇐ f))))))
    exL′ (_ ⊗> X) f = r⊗⇒ (eRL (r⇒⊗ (r⇒⊗ (exL′ X (r⊗⇒ f)))))
    exL′ (X <⊗ _) f = r⊗⇒ (eLL (r⇐⊗ (r⇒⊗ (exL′ X (r⊗⇐ f)))))


-- Defined types and rules for infixation
infix 50 _⇃_ _⇂_

abstract
  _⇃_ : Type → Type → Type
  B ⇃ A = ◇ □ (B ⇐ A)

  _⇂_ : Type → Type → Type
  A ⇂ B = ◇ □ (A ⇒ B)

  inL : ∀ (X : Context + +) {Y A B C}
    → X [ Y ] ⊢NL[ A ] → [ B ]⊢NL · C · → X [ · B ⇃ A · ⊗ Y ] ⊢NL · C ·
  inL X f g = ◇LL X (inL′ X (r⇐⊗ (r□◇ (↼ (□L (⇐L f g))))))
    where
    ◇LL : ∀ (X : Context + +) {Y A B Z}
      → X [ ◇ · □ (B ⇐ A) · ⊗ Y ] ⊢NL Z → X [ · B ⇃ A · ⊗ Y ] ⊢NL Z
    ◇LL []       f = r⇐⊗ (◇L    (r⊗⇐ f))
    ◇LL (X <⊗ _) f = r⇐⊗ (◇LL X (r⊗⇐ f))
    ◇LL (_ ⊗> X) f = r⇒⊗ (◇LL X (r⊗⇒ f))

    inL′ : ∀ (X : Context + +) {Y Z A B}
      → ◇ · □ (B ⇐ A) · ⊗ (X [ Y ]) ⊢NL Z → X [ ◇ · □ (B ⇐ A) · ⊗ Y ] ⊢NL Z
    inL′ []       f = f
    inL′ (_ ⊗> X) f = r⇒⊗ (inL′ X (r⊗⇒ (iRL f)))
    inL′ (X <⊗ _) f = r⇐⊗ (inL′ X (r⊗⇐ (iLL f)))

  inR : ∀ (X : Context + +) {Y A B C}
    → X [ Y ] ⊢NL[ A ] → [ B ]⊢NL · C · → X [ Y ⊗ · A ⇂ B · ] ⊢NL · C ·
  inR X f g = ◇LR X (inR′ X (r⇒⊗ (r□◇ (↼ (□L (⇒L f g))))))
    where
    ◇LR : ∀ (X : Context + +) {Y A B Z}
      → X [ Y ⊗ ◇ · □ (A ⇒ B) · ] ⊢NL Z → X [ Y ⊗ · A ⇂ B · ] ⊢NL Z
    ◇LR []       f = r⇒⊗ (◇L    (r⊗⇒ f))
    ◇LR (X <⊗ _) f = r⇐⊗ (◇LR X (r⊗⇐ f))
    ◇LR (_ ⊗> X) f = r⇒⊗ (◇LR X (r⊗⇒ f))

    inR′ : ∀ (X : Context + +) {Y Z A B}
      → (X [ Y ]) ⊗ ◇ · □ (A ⇒ B) · ⊢NL Z → X [ Y ⊗ ◇ · □ (A ⇒ B) · ] ⊢NL Z
    inR′ []       f = f
    inR′ (_ ⊗> X) f = r⇒⊗ (inR′ X (r⊗⇒ (iRR f)))
    inR′ (X <⊗ _) f = r⇐⊗ (inR′ X (r⊗⇐ (iLR f)))


-- Compute traces left by moving upwards using QR
TraceL : Context + + → Context + +
TraceL []       = []
TraceL (C ⊗> Γ) = C ⊗> (L ⊗> TraceL Γ)
TraceL (Γ <⊗ C) = (L ⊗> TraceL Γ) <⊗ C

TraceR : Context + + → Context + +
TraceR []       = []
TraceR (C ⊗> Γ) = C ⊗> (TraceR Γ <⊗ R)
TraceR (Γ <⊗ C) = (TraceR Γ <⊗ R) <⊗ C


-- Defined types and rules for moving upwards using QR
infix 50 _↙_ _↘_ _↗_ _↖_

abstract
  _↙_ : Type → Type → Type
  B ↙ A = ⬗ ◨ (B ⇐ A)

  _↘_ : Type → Type → Type
  A ↘ B = ⬗ ◨ (A ⇒ B)

  _↗_ : Type → Type → Type
  B ↗ A = B ⇐ ⬖ ◧ A

  _↖_ : Type → Type → Type
  A ↖ B = ⬖ ◧ A ⇒ B

  ↙L : ∀ (X : Context + +) {Y A B Z}
    → [ B ]⊢NL Z → TraceL X [ Y ] ⊢NL[ A ] → X [ · B ↙ A · ⊗ Y ] ⊢NL Z
  ↙L X f g = ⬗LL X (↙L′ X (r⇐⊗ (r◨⬗ (↼ (◨L (⇐L g f))))))
    where
    ⬗LL : ∀ (X : Context + +) {Y A B Z}
      → X [ ⬗ · ◨ (B ⇐ A) · ⊗ Y ] ⊢NL Z → X [ · B ↙ A · ⊗ Y ] ⊢NL Z
    ⬗LL []       f = r⇐⊗ (⬗L    (r⊗⇐ f))
    ⬗LL (X <⊗ _) f = r⇐⊗ (⬗LL X (r⊗⇐ f))
    ⬗LL (_ ⊗> X) f = r⇒⊗ (⬗LL X (r⊗⇒ f))
    ↙L′ : ∀ (X : Context + +) {Y A B Z}
        → ⬗ · ◨ (B ⇐ A) · ⊗ (TraceL X [ Y ]) ⊢NL Z → X [ ⬗ · ◨ (B ⇐ A) · ⊗ Y ] ⊢NL Z
    ↙L′ []       f = f
    ↙L′ (X <⊗ _) f = r⇐⊗ (↙L′ X (r⊗⇐ (↓LL f)))
    ↙L′ (_ ⊗> X) f = r⇒⊗ (↙L′ X (r⊗⇒ (↓RL f)))

  ↘L : ∀ (X : Context + +) {Y A B Z}
    → [ B ]⊢NL Z → TraceR X [ Y ] ⊢NL[ A ] → X [ Y ⊗ · A ↘ B · ] ⊢NL Z
  ↘L X f g = ⬗LR X (↘L′ X (r⇒⊗ (r◨⬗ (↼ (◨L (⇒L g f))))))
    where
    ⬗LR : ∀ (X : Context + +) {Y A B Z}
      → X [ Y ⊗ ⬗ · ◨ (A ⇒ B) · ] ⊢NL Z → X [ Y ⊗ · A ↘ B · ] ⊢NL Z
    ⬗LR []       f = r⇒⊗ (⬗L    (r⊗⇒ f))
    ⬗LR (X <⊗ _) f = r⇐⊗ (⬗LR X (r⊗⇐ f))
    ⬗LR (_ ⊗> X) f = r⇒⊗ (⬗LR X (r⊗⇒ f))
    ↘L′ : ∀ (X : Context + +) {Y A B Z}
      → (TraceR X [ Y ]) ⊗ ⬗ · ◨ (A ⇒ B) · ⊢NL Z → X [ Y ⊗ ⬗ · ◨ (A ⇒ B) · ] ⊢NL Z
    ↘L′ []       f = f
    ↘L′ (X <⊗ _) f = r⇐⊗ (↘L′ X (r⊗⇐ (↓LR f)))
    ↘L′ (_ ⊗> X) f = r⇒⊗ (↘L′ X (r⊗⇒ (↓RR f)))

  ↖L : ∀ (X : Context + +) {Y A B}
    → X [ · A · ⊗ Y ] ⊢NL · B · → TraceL X [ Y ] ⊢NL · A ↖ B ·
  ↖L X f = ⇒R (r⊗⇒ (r⇐⊗ (⬖L (r⊗⇐ (r⇒⊗ (↖L′ X f))))))
    where
    ↖L′ : ∀ (X : Context + +) {Y A Z}
      → X [ · A · ⊗ Y ] ⊢NL Z → TraceL X [ Y ] ⊢NL ⬖ · ◧ A · ⇒ Z
    ↖L′ []       f = r⊗⇒ (r⇐⊗ (r◧⬖ (↼ (◧L (↽ (r⊗⇐ f))))))
    ↖L′ (X <⊗ _) f = r⊗⇒ (↑LL (r⇐⊗ (r⇒⊗ (↖L′ X (r⊗⇐ f)))))
    ↖L′ (_ ⊗> X) f = r⊗⇒ (↑RL (r⇒⊗ (r⇒⊗ (↖L′ X (r⊗⇒ f)))))

  ↗L : ∀ (X : Context + +) {Y A B}
    → X [ Y ⊗ · A · ] ⊢NL · B · → TraceR X [ Y ] ⊢NL · B ↗ A ·
  ↗L X f = ⇐R (r⊗⇐ (r⇒⊗ (⬖L (r⊗⇒ (r⇐⊗ (↗L′ X f))))))
    where
    ↗L′ : ∀ (X : Context + +) {Y A Z}
      → X [ Y ⊗ · A · ] ⊢NL Z → TraceR X [ Y ] ⊢NL Z ⇐ ⬖ · ◧ A ·
    ↗L′ []       f = r⊗⇐ (r⇒⊗ (r◧⬖ (↼ (◧L (↽ (r⊗⇒ f))))))
    ↗L′ (X <⊗ _) f = r⊗⇐ (↑LR (r⇐⊗ (r⇐⊗ (↗L′ X (r⊗⇐ f)))))
    ↗L′ (_ ⊗> X) f = r⊗⇐ (↑RR (r⇒⊗ (r⇐⊗ (↗L′ X (r⊗⇒ f)))))


-- -}
-- -}
-- -}
-- -}
-- -}
