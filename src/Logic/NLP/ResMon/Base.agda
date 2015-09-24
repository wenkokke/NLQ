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


module Logic.NLP.ResMon.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.ResMon.Type         Atom
open import Logic.NLP.ResMon.Type.Context Atom
open import Logic.NLP.ResMon.Sequent      Atom


infix  1  NL_ _⊢NL_
mutual
  _⊢NL_ : Type → Type → Set ℓ
  A ⊢NL B = NL A ⊢ B

  data NL_ : Sequent → Set ℓ where

    ax  : ∀ {A}       → el A ⊢NL el A

    -- rules for monotonicity for (⟨⟩)
    m⟨⟩ : ∀ {A B}     → A ⊢NL B → ⟨ A ⟩ ⊢NL ⟨ B ⟩

    -- rules for residuation and monotonicity for (□ , ◇)
    m□  : ∀ {A B}     →   A ⊢NL   B → □ A ⊢NL □ B
    m◇  : ∀ {A B}     →   A ⊢NL   B → ◇ A ⊢NL ◇ B
    r□◇ : ∀ {A B}     →   A ⊢NL □ B → ◇ A ⊢NL   B
    r◇□ : ∀ {A B}     → ◇ A ⊢NL   B →   A ⊢NL □ B

    -- rules for residuation and monotonicity for (■ , ◆)
    m■  : ∀ {A B}     →   A ⊢NL   B → ■ A ⊢NL ■ B
    m◆  : ∀ {A B}     →   A ⊢NL   B → ◆ A ⊢NL ◆ B
    r■◆ : ∀ {A B}     →   A ⊢NL ■ B → ◆ A ⊢NL   B
    r◆■ : ∀ {A B}     → ◆ A ⊢NL   B →   A ⊢NL ■ B

    -- rules for residuation and monotonicity for (◨ , ⬗, ◧ , ⬖, L, R)
    m◨  : ∀ {A B}     →   A ⊢NL   B → ◨ A ⊢NL ◨ B
    m⬗  : ∀ {A B}     →   A ⊢NL   B → ⬗ A ⊢NL ⬗ B
    r◨⬗ : ∀ {A B}     →   A ⊢NL ◨ B → ⬗ A ⊢NL   B
    r⬗◨ : ∀ {A B}     → ⬗ A ⊢NL   B →   A ⊢NL ◨ B

    m◧  : ∀ {A B}     →   A ⊢NL   B → ◧ A ⊢NL ◧ B
    m⬖  : ∀ {A B}     →   A ⊢NL   B → ⬖ A ⊢NL ⬖ B
    r◧⬖ : ∀ {A B}     →   A ⊢NL ◧ B → ⬖ A ⊢NL   B
    r⬖◧ : ∀ {A B}     → ⬖ A ⊢NL   B →   A ⊢NL ◧ B

    mL  : L ⊢NL L
    mR  : R ⊢NL R

    -- left and right rules for (&)
    &L₁ : ∀ {A B C}   → A ⊢NL C → A & B ⊢NL C
    &L₂ : ∀ {A B C}   → B ⊢NL C → A & B ⊢NL C
    &R  : ∀ {A B C}   → A ⊢NL B → A ⊢NL C → A ⊢NL B & C

    -- rules for residuation and monotonicity for (⇐ , ⊗ , ⇒)
    m⊗  : ∀ {A B C D} → A ⊢NL B     → C ⊢NL D     → A ⊗ C ⊢NL B ⊗ D
    m⇒  : ∀ {A B C D} → A ⊢NL B     → C ⊢NL D     → B ⇒ C ⊢NL A ⇒ D
    m⇐  : ∀ {A B C D} → A ⊢NL B     → C ⊢NL D     → A ⇐ D ⊢NL B ⇐ C
    r⇒⊗ : ∀ {A B C}   → B ⊢NL A ⇒ C → A ⊗ B ⊢NL C
    r⊗⇒ : ∀ {A B C}   → A ⊗ B ⊢NL C → B ⊢NL A ⇒ C
    r⇐⊗ : ∀ {A B C}   → A ⊢NL C ⇐ B → A ⊗ B ⊢NL C
    r⊗⇐ : ∀ {A B C}   → A ⊗ B ⊢NL C → A ⊢NL C ⇐ B

    -- structural postulates for infixation
    iRR : ∀ {A B C D} → (A ⊗ B) ⊗ ◇ C ⊢NL D → A ⊗ (B ⊗ ◇ C) ⊢NL D
    iLR : ∀ {A B C D} → (A ⊗ B) ⊗ ◇ C ⊢NL D → (A ⊗ ◇ C) ⊗ B ⊢NL D
    iLL : ∀ {A B C D} → ◇ C ⊗ (B ⊗ A) ⊢NL D → (◇ C ⊗ B) ⊗ A ⊢NL D
    iRL : ∀ {A B C D} → ◇ C ⊗ (B ⊗ A) ⊢NL D → B ⊗ (◇ C ⊗ A) ⊢NL D

    -- structural postulates for extraction
    eRR : ∀ {A B C D} → A ⊗ (B ⊗ ◆ C) ⊢NL D → (A ⊗ B) ⊗ ◆ C ⊢NL D
    eLR : ∀ {A B C D} → (A ⊗ ◆ C) ⊗ B ⊢NL D → (A ⊗ B) ⊗ ◆ C ⊢NL D
    eLL : ∀ {A B C D} → (◆ C ⊗ B) ⊗ A ⊢NL D → ◆ C ⊗ (B ⊗ A) ⊢NL D
    eRL : ∀ {A B C D} → B ⊗ (◆ C ⊗ A) ⊢NL D → ◆ C ⊗ (B ⊗ A) ⊢NL D

    -- structural postulates for quantifier raising
    ↓RR : ∀ {A B C D} → (A ⊗ (B ⊗ R)) ⊗ ⬗ C ⊢NL D → A ⊗ (B ⊗ ⬗ C) ⊢NL D
    ↓LR : ∀ {A B C D} → ((A ⊗ R) ⊗ B) ⊗ ⬗ C ⊢NL D → (A ⊗ ⬗ C) ⊗ B ⊢NL D
    ↓LL : ∀ {A B C D} → ⬗ C ⊗ ((L ⊗ B) ⊗ A) ⊢NL D → (⬗ C ⊗ B) ⊗ A ⊢NL D
    ↓RL : ∀ {A B C D} → ⬗ C ⊗ (B ⊗ (L ⊗ A)) ⊢NL D → B ⊗ (⬗ C ⊗ A) ⊢NL D

    ↑RR : ∀ {A B C D} → A ⊗ (B ⊗ ⬖ C) ⊢NL D → (A ⊗ (B ⊗ R)) ⊗ ⬖ C ⊢NL D
    ↑LR : ∀ {A B C D} → (A ⊗ ⬖ C) ⊗ B ⊢NL D → ((A ⊗ R) ⊗ B) ⊗ ⬖ C ⊢NL D
    ↑LL : ∀ {A B C D} → (⬖ C ⊗ B) ⊗ A ⊢NL D → ⬖ C ⊗ ((L ⊗ B) ⊗ A) ⊢NL D
    ↑RL : ∀ {A B C D} → B ⊗ (⬖ C ⊗ A) ⊢NL D → ⬖ C ⊗ (B ⊗ (L ⊗ A)) ⊢NL D



-- Derived rule for identity, which holds as long as the type A only
-- connectives from the non-associative Lambek calculus `NL`.
ax′ : ∀ {A} → A ⊢NL A
ax′ {el  A} = ax
ax′ {⟨ A ⟩} = m⟨⟩ ax′
ax′ {□   A} = m□  ax′
ax′ {◇   A} = m◇  ax′
ax′ {■   A} = m■  ax′
ax′ {◆   A} = m◆  ax′
ax′ {◨   A} = m◨  ax′
ax′ {⬗   A} = m⬗  ax′
ax′ {◧   A} = m◧  ax′
ax′ {⬖   A} = m⬖  ax′
ax′ {L    } = mL
ax′ {R    } = mR
ax′ {A & B} = &R (&L₁ ax′) (&L₂ ax′)
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′


-- Defined rules for extraction
infix 50 _↾_ _↿_

abstract
  _↾_ : Type → Type → Type
  A ↾ B = A ⇐ ◆ ■ B

  _↿_ : Type → Type → Type
  B ↿ A = ◆ ■ B ⇒ A

  exR : ∀ (Γ : Context) {Δ A B} → Γ [ Δ ⊗ B ] ⊢NL A → Γ [ Δ ] ⊢NL A ↾ B
  exR []       f = r⊗⇐ (r⇒⊗ (r■◆ (m■ (r⊗⇒ f))))
  exR (_ ⊗> Γ) f = r⊗⇐ (eRR (r⇒⊗ (r⇐⊗ (exR Γ (r⊗⇒ f)))))
  exR (Γ <⊗ _) f = r⊗⇐ (eLR (r⇐⊗ (r⇐⊗ (exR Γ (r⊗⇐ f)))))

  exL : ∀ (Γ : Context) {Δ A B} → Γ [ B ⊗ Δ ] ⊢NL A → Γ [ Δ ] ⊢NL B ↿ A
  exL []       f = r⊗⇒ (r⇐⊗ (r■◆ (m■ (r⊗⇐ f))))
  exL (_ ⊗> Γ) f = r⊗⇒ (eRL (r⇒⊗ (r⇒⊗ (exL Γ (r⊗⇒ f)))))
  exL (Γ <⊗ _) f = r⊗⇒ (eLL (r⇐⊗ (r⇒⊗ (exL Γ (r⊗⇐ f)))))


-- Defined types and rules for infixation
infix 50 _⇃_ _⇂_

abstract
  _⇃_ : Type → Type → Type
  B ⇃ A = ◇ □ (B ⇐ A)

  _⇂_ : Type → Type → Type
  A ⇂ B = ◇ □ (A ⇒ B)

  inL : ∀ (Δ : Context) {Γ A B C}
      → B ⊢NL C → Δ [ Γ ] ⊢NL A → Δ [ B ⇃ A ⊗ Γ ] ⊢NL C
  inL Δ f g = upL Δ (r⇐⊗ (r□◇ (m□ (m⇐ f g))))
    where
    upL : ∀ (Δ : Context) {Γ A B C}
        → B ⇃ A ⊗ Δ [ Γ ] ⊢NL C → Δ [ B ⇃ A ⊗ Γ ] ⊢NL C
    upL []       f = f
    upL (_ ⊗> Δ) f = r⇒⊗ (upL Δ (r⊗⇒ (iRL f)))
    upL (Δ <⊗ _) f = r⇐⊗ (upL Δ (r⊗⇐ (iLL f)))

  inR : ∀ (Δ : Context) {Γ A B C}
      → B ⊢NL C → Δ [ Γ ] ⊢NL A → Δ [ Γ ⊗ A ⇂ B ] ⊢NL C
  inR Δ f g = upR Δ (r⇒⊗ (r□◇ (m□ (m⇒ g f))))
    where
    upR : ∀ (Δ : Context) {Γ A B C}
        → Δ [ Γ ] ⊗ A ⇂ B ⊢NL C → Δ [ Γ ⊗ A ⇂ B ] ⊢NL C
    upR []       f = f
    upR (_ ⊗> Δ) f = r⇒⊗ (upR Δ (r⊗⇒ (iRR f)))
    upR (Δ <⊗ _) f = r⇐⊗ (upR Δ (r⊗⇐ (iLR f)))


-- Compute traces left by moving upwards using QR
TraceL : Context → Context
TraceL []       = []
TraceL (C ⊗> Γ) = C ⊗> (L ⊗> TraceL Γ)
TraceL (Γ <⊗ C) = (L ⊗> TraceL Γ) <⊗ C

TraceR : Context → Context
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

  ↙L : ∀ (Δ : Context) {Γ A B C}
    → B ⊢NL C → TraceL Δ [ Γ ] ⊢NL A → Δ [ B ↙ A ⊗ Γ ] ⊢NL C
  ↙L Δ f g = upL′ Δ (r⇐⊗ (r◨⬗ (m◨ (m⇐ f g))))
    where
    upL′ : ∀ (Δ : Context) {Γ A B}
         → ⬗ A ⊗ TraceL Δ [ Γ ] ⊢NL B → Δ [ ⬗ A ⊗ Γ ] ⊢NL B
    upL′ []       f = f
    upL′ (_ ⊗> Δ) f = r⇒⊗ (upL′ Δ (r⊗⇒ (↓RL f)))
    upL′ (Δ <⊗ _) f = r⇐⊗ (upL′ Δ (r⊗⇐ (↓LL f)))

  ↘L : ∀ (Δ : Context) {Γ A B C}
    → B ⊢NL C → TraceR Δ [ Γ ] ⊢NL A → Δ [ Γ ⊗ A ↘ B ] ⊢NL C
  ↘L Δ f g = upR′ Δ (r⇒⊗ (r◨⬗ (m◨ (m⇒ g f))))
    where
    upR′ : ∀ (Δ : Context) {Γ A B}
         → TraceR Δ [ Γ ] ⊗ ⬗ A ⊢NL B → Δ [ Γ ⊗ ⬗ A ] ⊢NL B
    upR′ []       f = f
    upR′ (_ ⊗> Δ) f = r⇒⊗ (upR′ Δ (r⊗⇒ (↓RR f)))
    upR′ (Δ <⊗ _) f = r⇐⊗ (upR′ Δ (r⊗⇐ (↓LR f)))

  ↖L : ∀ (Δ : Context) {Γ A B}
    → Δ [ A ⊗ Γ ] ⊢NL B → TraceL Δ [ Γ ] ⊢NL A ↖ B
  ↖L Δ f = r⊗⇒ (dnL′ Δ f)
    where
    dnL′ : ∀ (Δ : Context) {Γ A B}
         → Δ [ A ⊗ Γ ] ⊢NL B → ⬖ ◧ A ⊗ TraceL Δ [ Γ ] ⊢NL B
    dnL′ []       f = r⇐⊗ (r◧⬖ (m◧ (r⊗⇐ f)))
    dnL′ (_ ⊗> Δ) f = ↑RL (r⇒⊗ (dnL′ Δ (r⊗⇒ f)))
    dnL′ (Δ <⊗ _) f = ↑LL (r⇐⊗ (dnL′ Δ (r⊗⇐ f)))

  ↗L : ∀ (Δ : Context) {Γ A B}
    → Δ [ Γ ⊗ A ] ⊢NL B → TraceR Δ [ Γ ] ⊢NL B ↗ A
  ↗L Δ f = r⊗⇐ (dnR′ Δ f)
    where
    dnR′ : ∀ (Δ : Context) {Γ A B}
         → Δ [ Γ ⊗ A ] ⊢NL B → TraceR Δ [ Γ ] ⊗ ⬖ ◧ A ⊢NL B
    dnR′ []       f = r⇒⊗ (r◧⬖ (m◧ (r⊗⇒ f)))
    dnR′ (_ ⊗> Δ) f = ↑RR (r⇒⊗ (dnR′ Δ (r⊗⇒ f)))
    dnR′ (Δ <⊗ _) f = ↑LR (r⇐⊗ (dnR′ Δ (r⊗⇐ f)))


⇒L : ∀ (Δ : Context) {Γ A B C}
   → Γ ⊢NL A → Δ [ B ] ⊢NL C → Δ [ Γ ⊗ (A ⇒ B) ] ⊢NL C
⇒L []       f g = r⇒⊗ (m⇒ f g)
⇒L (_ ⊗> Δ) f g = r⇒⊗ (⇒L Δ f (r⊗⇒ g))
⇒L (Δ <⊗ _) f g = r⇐⊗ (⇒L Δ f (r⊗⇐ g))

⇒R : ∀ {Γ A B} → A ⊗ Γ ⊢NL B → Γ ⊢NL A ⇒ B
⇒R f = r⊗⇒ f

⇐L : ∀ (Δ : Context) {Γ A B C}
   → Γ ⊢NL A → Δ [ B ] ⊢NL C → Δ [ (B ⇐ A) ⊗ Γ ] ⊢NL C
⇐L []       f g = r⇐⊗ (m⇐ g f)
⇐L (_ ⊗> Δ) f g = r⇒⊗ (⇐L Δ f (r⊗⇒ g))
⇐L (Δ <⊗ _) f g = r⇐⊗ (⇐L Δ f (r⊗⇐ g))

⇐R : ∀ {Γ A B} → Γ ⊗ A ⊢NL B → Γ ⊢NL B ⇐ A
⇐R f = r⊗⇐ f


-- Symmetries that do hold
_⋈ : ∀ {J} → NL J → NL (J ⋈ʲ)
ax      ⋈ = ax
m⟨⟩ f   ⋈ = m⟨⟩ (f ⋈)
m□  f   ⋈ = m□  (f ⋈)
m◇  f   ⋈ = m◇  (f ⋈)
r□◇ f   ⋈ = r□◇ (f ⋈)
r◇□ f   ⋈ = r◇□ (f ⋈)
m■  f   ⋈ = m■  (f ⋈)
m◆  f   ⋈ = m◆  (f ⋈)
r■◆ f   ⋈ = r■◆ (f ⋈)
r◆■ f   ⋈ = r◆■ (f ⋈)
m◨  f   ⋈ = m◨  (f ⋈)
m⬗  f   ⋈ = m⬗  (f ⋈)
r◨⬗ f   ⋈ = r◨⬗ (f ⋈)
r⬗◨ f   ⋈ = r⬗◨ (f ⋈)
m◧  f   ⋈ = m◧  (f ⋈)
m⬖  f   ⋈ = m⬖  (f ⋈)
r◧⬖ f   ⋈ = r◧⬖ (f ⋈)
r⬖◧ f   ⋈ = r⬖◧ (f ⋈)
mL      ⋈ = mR
mR      ⋈ = mL
&L₁ f   ⋈ = &L₁ (f ⋈)
&L₂ f   ⋈ = &L₂ (f ⋈)
&R  f g ⋈ = &R  (f ⋈) (g ⋈)
m⊗  f g ⋈ = m⊗  (g ⋈) (f ⋈)
m⇒  f g ⋈ = m⇐  (g ⋈) (f ⋈)
m⇐  f g ⋈ = m⇒  (g ⋈) (f ⋈)
r⇒⊗ f   ⋈ = r⇐⊗ (f ⋈)
r⊗⇒ f   ⋈ = r⊗⇐ (f ⋈)
r⇐⊗ f   ⋈ = r⇒⊗ (f ⋈)
r⊗⇐ f   ⋈ = r⊗⇒ (f ⋈)
iRR f   ⋈ = iLL (f ⋈)
iLR f   ⋈ = iRL (f ⋈)
iLL f   ⋈ = iRR (f ⋈)
iRL f   ⋈ = iLR (f ⋈)
eRR f   ⋈ = eLL (f ⋈)
eLR f   ⋈ = eRL (f ⋈)
eLL f   ⋈ = eRR (f ⋈)
eRL f   ⋈ = eLR (f ⋈)
↓LL f   ⋈ = ↓RR (f ⋈)
↓RL f   ⋈ = ↓LR (f ⋈)
↓RR f   ⋈ = ↓LL (f ⋈)
↓LR f   ⋈ = ↓RL (f ⋈)
↑LL f   ⋈ = ↑RR (f ⋈)
↑RL f   ⋈ = ↑LR (f ⋈)
↑RR f   ⋈ = ↑LL (f ⋈)
↑LR f   ⋈ = ↑RL (f ⋈)


_⋈⁻¹ : ∀ {J} → NL (J ⋈ʲ) → NL J
_⋈⁻¹ {J} f = P.subst NL_ (⋈ʲ-inv J) (f ⋈)


infix 5 is-ax_ is-ax?_

-- Heterogeneous equality of proofs, checking if the proof is equal to
-- the identity proof.
is-ax_ : ∀ {A B} (f : A ⊢NL B) → Set ℓ
is-ax_ f = ∃ (λ A → f ≅ ax {A})


-- Decision procedure for heterogeneous equality of proofs, checking
-- if the proof is equal to the identity proof.
is-ax?_ : ∀ {A B} (f : A ⊢NL B) → Dec (is-ax f)
is-ax? ax      = yes (_ , H.refl)
is-ax? m⟨⟩ _   = no (λ {(_ , ())})
is-ax? m□  _   = no (λ {(_ , ())})
is-ax? m◇  _   = no (λ {(_ , ())})
is-ax? r□◇ _   = no (λ {(_ , ())})
is-ax? r◇□ _   = no (λ {(_ , ())})
is-ax? m■  _   = no (λ {(_ , ())})
is-ax? m◆  _   = no (λ {(_ , ())})
is-ax? r■◆ _   = no (λ {(_ , ())})
is-ax? r◆■ _   = no (λ {(_ , ())})
is-ax? m◨  _   = no (λ {(_ , ())})
is-ax? m⬗  _   = no (λ {(_ , ())})
is-ax? r◨⬗ _   = no (λ {(_ , ())})
is-ax? r⬗◨ _   = no (λ {(_ , ())})
is-ax? m◧  _   = no (λ {(_ , ())})
is-ax? m⬖  _   = no (λ {(_ , ())})
is-ax? r◧⬖ _   = no (λ {(_ , ())})
is-ax? r⬖◧ _   = no (λ {(_ , ())})
is-ax? mL      = no (λ {(_ , ())})
is-ax? mR      = no (λ {(_ , ())})
is-ax? &L₁ _   = no (λ {(_ , ())})
is-ax? &L₂ _   = no (λ {(_ , ())})
is-ax? &R  _ _ = no (λ {(_ , ())})
is-ax? m⊗  _ _ = no (λ {(_ , ())})
is-ax? m⇒  _ _ = no (λ {(_ , ())})
is-ax? m⇐  _ _ = no (λ {(_ , ())})
is-ax? r⇒⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇒ _   = no (λ {(_ , ())})
is-ax? r⇐⊗ _   = no (λ {(_ , ())})
is-ax? r⊗⇐ _   = no (λ {(_ , ())})
is-ax? iRR _   = no (λ {(_ , ())})
is-ax? iLR _   = no (λ {(_ , ())})
is-ax? iLL _   = no (λ {(_ , ())})
is-ax? iRL _   = no (λ {(_ , ())})
is-ax? eRR _   = no (λ {(_ , ())})
is-ax? eLR _   = no (λ {(_ , ())})
is-ax? eLL _   = no (λ {(_ , ())})
is-ax? eRL _   = no (λ {(_ , ())})
is-ax? ↓LL _   = no (λ {(_ , ())})
is-ax? ↓RL _   = no (λ {(_ , ())})
is-ax? ↓RR _   = no (λ {(_ , ())})
is-ax? ↓LR _   = no (λ {(_ , ())})
is-ax? ↑LL _   = no (λ {(_ , ())})
is-ax? ↑RL _   = no (λ {(_ , ())})
is-ax? ↑RR _   = no (λ {(_ , ())})
is-ax? ↑LR _   = no (λ {(_ , ())})


-- -}
-- -}
-- -}
-- -}
-- -}
