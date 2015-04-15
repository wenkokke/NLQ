------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Intuitionistic.Ordered.NLCL.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Intuitionistic.Ordered.NLCL.Type                   Univ
open import Logic.Intuitionistic.Ordered.NLCL.Type.Context.Polarised Univ
open import Logic.Intuitionistic.Ordered.NLCL.Judgement              Univ


infix 1 NL_

data NL_ : Judgement → Set ℓ where

  ax  : ∀ {A} → NL el A ⊢ el A

  -- rules for (⇐ , ⊗ , ⇒)
  m⊗  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⊗ C ⊢ B ⊗ D
  m⇒  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇒ C ⊢ A ⇒ D
  m⇐  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇐ D ⊢ B ⇐ C
  r⇒⊗ : ∀ {A B C}   → NL B ⊢ A ⇒ C → NL A ⊗ B ⊢ C
  r⊗⇒ : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL B ⊢ A ⇒ C
  r⇐⊗ : ∀ {A B C}   → NL A ⊢ C ⇐ B → NL A ⊗ B ⊢ C
  r⊗⇐ : ∀ {A B C}   → NL A ⊗ B ⊢ C → NL A ⊢ C ⇐ B

  -- rules for (⇐ , ⊗ , ⇒)
  m∘  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ∘ C ⊢ B ∘ D
  m⇨  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL B ⇨ C ⊢ A ⇨ D
  m⇦  : ∀ {A B C D} → NL A ⊢ B → NL C ⊢ D → NL A ⇦ D ⊢ B ⇦ C
  r⇨∘ : ∀ {A B C}   → NL B ⊢ A ⇨ C → NL A ∘ B ⊢ C
  r∘⇨ : ∀ {A B C}   → NL A ∘ B ⊢ C → NL B ⊢ A ⇨ C
  r⇦∘ : ∀ {A B C}   → NL A ⊢ C ⇦ B → NL A ∘ B ⊢ C
  r∘⇦ : ∀ {A B C}   → NL A ∘ B ⊢ C → NL A ⊢ C ⇦ B

  -- rules for (I , L , R)
  mI  : NL I ⊢ I
  mL  : NL L ⊢ L
  mR  : NL R ⊢ R

  Iᵢ  : ∀ {A B}     → NL A ⊢ B → NL A ∘ I ⊢ B
  Iₑ  : ∀ {A B}     → NL A ∘ I ⊢ B → NL A ⊢ B
  Lᵢ  : ∀ {A B C D} → NL A ⊗ (B ∘ C) ⊢ D → NL B ∘ ((L ⊗ A) ⊗ C) ⊢ D
  Lₑ  : ∀ {A B C D} → NL B ∘ ((L ⊗ A) ⊗ C) ⊢ D → NL A ⊗ (B ∘ C) ⊢ D
  Rᵢ  : ∀ {A B C D} → NL (A ∘ B) ⊗ C ⊢ D → NL A ∘ ((R ⊗ B) ⊗ C) ⊢ D
  Rₑ  : ∀ {A B C D} → NL A ∘ ((R ⊗ B) ⊗ C) ⊢ D → NL (A ∘ B) ⊗ C ⊢ D


-- Derive logical rules given in Barker and Shan (2014).
ax′ : ∀ {A} → NL A ⊢ A
ax′ {el  A} = ax
ax′ {A ⊗ B} = m⊗ ax′ ax′
ax′ {A ⇒ B} = m⇒ ax′ ax′
ax′ {A ⇐ B} = m⇐ ax′ ax′
ax′ {A ∘ B} = m∘ ax′ ax′
ax′ {A ⇨ B} = m⇨ ax′ ax′
ax′ {A ⇦ B} = m⇦ ax′ ax′
ax′ {I}     = mI
ax′ {L}     = mL
ax′ {R}     = mR

⇒ᴸ′ : ∀ (Σ : Context +) {Γ A B C} → NL Γ ⊢ A → NL Σ [ B ] ⊢ C → NL Σ [ Γ ⊗ A ⇒ B ] ⊢ C
⇒ᴸ′    []    f g = r⇒⊗ (m⇒ f g)
⇒ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇒ᴸ′ Σ f (r⊗⇒ g))
⇒ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇒ᴸ′ Σ f (r∘⇨ g))
⇒ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇒ᴸ′ Σ f (r⊗⇐ g))
⇒ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇒ᴸ′ Σ f (r∘⇦ g))

⇒ᴿ′ : ∀ {Γ A B} → NL A ⊗ Γ ⊢ B → NL Γ ⊢ A ⇒ B
⇒ᴿ′ f = r⊗⇒ f

⇐ᴸ′ : ∀ (Σ : Context +) {Γ A B C} → NL Γ ⊢ A → NL Σ [ B ] ⊢ C → NL Σ [ B ⇐ A ⊗ Γ ] ⊢ C
⇐ᴸ′    []    f g = r⇐⊗ (m⇐ g f)
⇐ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇐ᴸ′ Σ f (r⊗⇒ g))
⇐ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇐ᴸ′ Σ f (r∘⇨ g))
⇐ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇐ᴸ′ Σ f (r⊗⇐ g))
⇐ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇐ᴸ′ Σ f (r∘⇦ g))

⇐ᴿ′ : ∀ {Γ A B} → NL Γ ⊗ A ⊢ B → NL Γ ⊢ B ⇐ A
⇐ᴿ′ f = r⊗⇐ f

⇨ᴸ′ : ∀ (Σ : Context +) {Γ A B C} → NL Γ ⊢ A → NL Σ [ B ] ⊢ C → NL Σ [ Γ ∘ A ⇨ B ] ⊢ C
⇨ᴸ′    []    f g = r⇨∘ (m⇨ f g)
⇨ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇨ᴸ′ Σ f (r⊗⇒ g))
⇨ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇨ᴸ′ Σ f (r∘⇨ g))
⇨ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇨ᴸ′ Σ f (r⊗⇐ g))
⇨ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇨ᴸ′ Σ f (r∘⇦ g))

⇨ᴿ′ : ∀ {Γ A B} → NL A ∘ Γ ⊢ B → NL Γ ⊢ A ⇨ B
⇨ᴿ′ f = r∘⇨ f

⇦ᴸ′ : ∀ (Σ : Context +) {Γ A B C} → NL Γ ⊢ A → NL Σ [ B ] ⊢ C → NL Σ [ B ⇦ A ∘ Γ ] ⊢ C
⇦ᴸ′    []    f g = r⇦∘ (m⇦ g f)
⇦ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇦ᴸ′ Σ f (r⊗⇒ g))
⇦ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇦ᴸ′ Σ f (r∘⇨ g))
⇦ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇦ᴸ′ Σ f (r⊗⇐ g))
⇦ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇦ᴸ′ Σ f (r∘⇦ g))

⇦ᴿ′ : ∀ {Γ A B} → NL Γ ∘ A ⊢ B → NL Γ ⊢ B ⇦ A
⇦ᴿ′ f = r∘⇦ f

Iᵢ′ : ∀ (Σ : Context +) {A B} → NL Σ [ A ] ⊢ B → NL Σ [ A ∘ I ] ⊢ B
Iᵢ′ [] f = Iᵢ f
Iᵢ′ (_ ⊗> Σ) f = r⇒⊗ (Iᵢ′ Σ (r⊗⇒ f))
Iᵢ′ (_ ∘> Σ) f = r⇨∘ (Iᵢ′ Σ (r∘⇨ f))
Iᵢ′ (Σ <⊗ _) f = r⇐⊗ (Iᵢ′ Σ (r⊗⇐ f))
Iᵢ′ (Σ <∘ _) f = r⇦∘ (Iᵢ′ Σ (r∘⇦ f))

Iₑ′ : ∀ (Σ : Context +) {A B} → NL Σ [ A ] ∘ I ⊢ B → NL Σ [ A ] ⊢ B
Iₑ′ [] f = Iₑ f
Iₑ′ (_ ⊗> Σ) f = Iₑ f
Iₑ′ (_ ∘> Σ) f = Iₑ f
Iₑ′ (Σ <⊗ _) f = Iₑ f
Iₑ′ (Σ <∘ _) f = Iₑ f

Lᵢ′ : ∀ (Σ : Context +) {A B C D} → NL Σ [ A ⊗ (B ∘ C) ] ⊢ D → NL Σ [ B ∘ ((L ⊗ A) ⊗ C) ] ⊢ D
Lᵢ′ [] f = Lᵢ f
Lᵢ′ (_ ⊗> Σ) f = r⇒⊗ (Lᵢ′ Σ (r⊗⇒ f))
Lᵢ′ (_ ∘> Σ) f = r⇨∘ (Lᵢ′ Σ (r∘⇨ f))
Lᵢ′ (Σ <⊗ _) f = r⇐⊗ (Lᵢ′ Σ (r⊗⇐ f))
Lᵢ′ (Σ <∘ _) f = r⇦∘ (Lᵢ′ Σ (r∘⇦ f))

Lₑ′ : ∀ (Σ : Context +) {A B C D} → NL Σ [ B ∘ ((L ⊗ A) ⊗ C) ] ⊢ D → NL Σ [ A ⊗ (B ∘ C) ] ⊢ D
Lₑ′ [] f = Lₑ f
Lₑ′ (_ ⊗> Σ) f = r⇒⊗ (Lₑ′ Σ (r⊗⇒ f))
Lₑ′ (_ ∘> Σ) f = r⇨∘ (Lₑ′ Σ (r∘⇨ f))
Lₑ′ (Σ <⊗ _) f = r⇐⊗ (Lₑ′ Σ (r⊗⇐ f))
Lₑ′ (Σ <∘ _) f = r⇦∘ (Lₑ′ Σ (r∘⇦ f))

Rᵢ′ : ∀ (Σ : Context +) {A B C D} → NL Σ [ (A ∘ B) ⊗ C ] ⊢ D → NL Σ [ A ∘ ((R ⊗ B) ⊗ C) ] ⊢ D
Rᵢ′ [] f = Rᵢ f
Rᵢ′ (_ ⊗> Σ) f = r⇒⊗ (Rᵢ′ Σ (r⊗⇒ f))
Rᵢ′ (_ ∘> Σ) f = r⇨∘ (Rᵢ′ Σ (r∘⇨ f))
Rᵢ′ (Σ <⊗ _) f = r⇐⊗ (Rᵢ′ Σ (r⊗⇐ f))
Rᵢ′ (Σ <∘ _) f = r⇦∘ (Rᵢ′ Σ (r∘⇦ f))

Rₑ′ : ∀ (Σ : Context +) {A B C D} → NL Σ [ A ∘ ((R ⊗ B) ⊗ C) ] ⊢ D → NL Σ [ (A ∘ B) ⊗ C ] ⊢ D
Rₑ′ [] f = Rₑ f
Rₑ′ (_ ⊗> Σ) f = r⇒⊗ (Rₑ′ Σ (r⊗⇒ f))
Rₑ′ (_ ∘> Σ) f = r⇨∘ (Rₑ′ Σ (r∘⇨ f))
Rₑ′ (Σ <⊗ _) f = r⇐⊗ (Rₑ′ Σ (r⊗⇐ f))
Rₑ′ (Σ <∘ _) f = r⇦∘ (Rₑ′ Σ (r∘⇦ f))
