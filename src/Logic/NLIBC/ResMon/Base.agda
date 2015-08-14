------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.NLIBC.ResMon.Base {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.NLIBC.Type                   Atom
open import Logic.NLIBC.Type.Context.Polarised Atom
open import Logic.NLIBC.ResMon.Judgement       Atom


infix 1 NL_

data NL_ : Judgement → Set ℓ where

  ax  : ∀ {x} → NL el x ⊢ el x

  -- rules for (⇐ , ⊗ , ⇒)
  m⊗  : ∀ {x y z w} → NL x ⊢ y → NL z ⊢ w → NL x ⊗ z ⊢ y ⊗ w
  m⇒  : ∀ {x y z w} → NL x ⊢ y → NL z ⊢ w → NL y ⇒ z ⊢ x ⇒ w
  m⇐  : ∀ {x y z w} → NL x ⊢ y → NL z ⊢ w → NL x ⇐ w ⊢ y ⇐ z
  r⇒⊗ : ∀ {x y z}   → NL y ⊢ x ⇒ z → NL x ⊗ y ⊢ z
  r⊗⇒ : ∀ {x y z}   → NL x ⊗ y ⊢ z → NL y ⊢ x ⇒ z
  r⇐⊗ : ∀ {x y z}   → NL x ⊢ z ⇐ y → NL x ⊗ y ⊢ z
  r⊗⇐ : ∀ {x y z}   → NL x ⊗ y ⊢ z → NL x ⊢ z ⇐ y

  -- rules for (⇦ , ∘ , ⇨)
  m∘  : ∀ {x y z w} → NL x ⊢ y → NL z ⊢ w → NL x ∘ z ⊢ y ∘ w
  m⇨  : ∀ {x y z w} → NL x ⊢ y → NL z ⊢ w → NL y ⇨ z ⊢ x ⇨ w
  m⇦  : ∀ {x y z w} → NL x ⊢ y → NL z ⊢ w → NL x ⇦ w ⊢ y ⇦ z
  r⇨∘ : ∀ {x y z}   → NL y ⊢ x ⇨ z → NL x ∘ y ⊢ z
  r∘⇨ : ∀ {x y z}   → NL x ∘ y ⊢ z → NL y ⊢ x ⇨ z
  r⇦∘ : ∀ {x y z}   → NL x ⊢ z ⇦ y → NL x ∘ y ⊢ z
  r∘⇦ : ∀ {x y z}   → NL x ∘ y ⊢ z → NL x ⊢ z ⇦ y

  -- rules for (I , B , C)
  mI  : NL I ⊢ I
  mB  : NL B ⊢ B
  mC  : NL C ⊢ C

  Iᵢ  : ∀ {x y}     → NL x ∘ I ⊢ y → NL x ⊢ y
  Iₑ  : ∀ {x y}     → NL x ⊢ y → NL x ∘ I ⊢ y
  Bᵢ  : ∀ {x y z w} → NL y ∘ ((B ⊗ x) ⊗ z) ⊢ w → NL x ⊗ (y ∘ z) ⊢ w
  Bₑ  : ∀ {x y z w} → NL x ⊗ (y ∘ z) ⊢ w → NL y ∘ ((B ⊗ x) ⊗ z) ⊢ w
  Cᵢ  : ∀ {x y z w} → NL x ∘ ((C ⊗ y) ⊗ z) ⊢ w → NL (x ∘ y) ⊗ z ⊢ w
  Cₑ  : ∀ {x y z w} → NL (x ∘ y) ⊗ z ⊢ w → NL x ∘ ((C ⊗ y) ⊗ z) ⊢ w


-- werive logical rules given in yarker and Shan (2014).
ax′ : ∀ {x} → NL x ⊢ x
ax′ {el  x} = ax
ax′ {x ⊗ y} = m⊗ ax′ ax′
ax′ {x ⇒ y} = m⇒ ax′ ax′
ax′ {x ⇐ y} = m⇐ ax′ ax′
ax′ {x ∘ y} = m∘ ax′ ax′
ax′ {x ⇨ y} = m⇨ ax′ ax′
ax′ {x ⇦ y} = m⇦ ax′ ax′
ax′ {I}     = mI
ax′ {B}     = mB
ax′ {C}     = mC

⇒ᴸ′ : ∀ (Σ : Context +) {Γ x y z} → NL Γ ⊢ x → NL Σ [ y ] ⊢ z → NL Σ [ Γ ⊗ x ⇒ y ] ⊢ z
⇒ᴸ′    []    f g = r⇒⊗ (m⇒ f g)
⇒ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇒ᴸ′ Σ f (r⊗⇒ g))
⇒ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇒ᴸ′ Σ f (r∘⇨ g))
⇒ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇒ᴸ′ Σ f (r⊗⇐ g))
⇒ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇒ᴸ′ Σ f (r∘⇦ g))

⇒ᴿ′ : ∀ {Γ x y} → NL x ⊗ Γ ⊢ y → NL Γ ⊢ x ⇒ y
⇒ᴿ′ f = r⊗⇒ f

⇐ᴸ′ : ∀ (Σ : Context +) {Γ x y z} → NL Γ ⊢ x → NL Σ [ y ] ⊢ z → NL Σ [ y ⇐ x ⊗ Γ ] ⊢ z
⇐ᴸ′    []    f g = r⇐⊗ (m⇐ g f)
⇐ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇐ᴸ′ Σ f (r⊗⇒ g))
⇐ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇐ᴸ′ Σ f (r∘⇨ g))
⇐ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇐ᴸ′ Σ f (r⊗⇐ g))
⇐ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇐ᴸ′ Σ f (r∘⇦ g))

⇐ᴿ′ : ∀ {Γ x y} → NL Γ ⊗ x ⊢ y → NL Γ ⊢ y ⇐ x
⇐ᴿ′ f = r⊗⇐ f

⇨ᴸ′ : ∀ (Σ : Context +) {Γ x y z} → NL Γ ⊢ x → NL Σ [ y ] ⊢ z → NL Σ [ Γ ∘ x ⇨ y ] ⊢ z
⇨ᴸ′    []    f g = r⇨∘ (m⇨ f g)
⇨ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇨ᴸ′ Σ f (r⊗⇒ g))
⇨ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇨ᴸ′ Σ f (r∘⇨ g))
⇨ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇨ᴸ′ Σ f (r⊗⇐ g))
⇨ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇨ᴸ′ Σ f (r∘⇦ g))

⇨ᴿ′ : ∀ {Γ x y} → NL x ∘ Γ ⊢ y → NL Γ ⊢ x ⇨ y
⇨ᴿ′ f = r∘⇨ f

⇦ᴸ′ : ∀ (Σ : Context +) {Γ x y z} → NL Γ ⊢ x → NL Σ [ y ] ⊢ z → NL Σ [ y ⇦ x ∘ Γ ] ⊢ z
⇦ᴸ′    []    f g = r⇦∘ (m⇦ g f)
⇦ᴸ′ (_ ⊗> Σ) f g = r⇒⊗ (⇦ᴸ′ Σ f (r⊗⇒ g))
⇦ᴸ′ (_ ∘> Σ) f g = r⇨∘ (⇦ᴸ′ Σ f (r∘⇨ g))
⇦ᴸ′ (Σ <⊗ _) f g = r⇐⊗ (⇦ᴸ′ Σ f (r⊗⇐ g))
⇦ᴸ′ (Σ <∘ _) f g = r⇦∘ (⇦ᴸ′ Σ f (r∘⇦ g))

⇦ᴿ′ : ∀ {Γ x y} → NL Γ ∘ x ⊢ y → NL Γ ⊢ y ⇦ x
⇦ᴿ′ f = r∘⇦ f

Iᵢ′ : ∀ (Σ : Context +) {x y} → NL Σ [ x ] ∘ I ⊢ y → NL Σ [ x ] ⊢ y
Iᵢ′ [] f = Iᵢ f
Iᵢ′ (_ ⊗> Σ) f = Iᵢ f
Iᵢ′ (_ ∘> Σ) f = Iᵢ f
Iᵢ′ (Σ <⊗ _) f = Iᵢ f
Iᵢ′ (Σ <∘ _) f = Iᵢ f

Iₑ′ : ∀ (Σ : Context +) {x y} → NL Σ [ x ] ⊢ y → NL Σ [ x ∘ I ] ⊢ y
Iₑ′ [] f = Iₑ f
Iₑ′ (_ ⊗> Σ) f = r⇒⊗ (Iₑ′ Σ (r⊗⇒ f))
Iₑ′ (_ ∘> Σ) f = r⇨∘ (Iₑ′ Σ (r∘⇨ f))
Iₑ′ (Σ <⊗ _) f = r⇐⊗ (Iₑ′ Σ (r⊗⇐ f))
Iₑ′ (Σ <∘ _) f = r⇦∘ (Iₑ′ Σ (r∘⇦ f))

Bᵢ′ : ∀ (Σ : Context +) {x y z w} → NL Σ [ y ∘ ((B ⊗ x) ⊗ z) ] ⊢ w → NL Σ [ x ⊗ (y ∘ z) ] ⊢ w
Bᵢ′ [] f = Bᵢ f
Bᵢ′ (_ ⊗> Σ) f = r⇒⊗ (Bᵢ′ Σ (r⊗⇒ f))
Bᵢ′ (_ ∘> Σ) f = r⇨∘ (Bᵢ′ Σ (r∘⇨ f))
Bᵢ′ (Σ <⊗ _) f = r⇐⊗ (Bᵢ′ Σ (r⊗⇐ f))
Bᵢ′ (Σ <∘ _) f = r⇦∘ (Bᵢ′ Σ (r∘⇦ f))

Bₑ′ : ∀ (Σ : Context +) {x y z w} → NL Σ [ x ⊗ (y ∘ z) ] ⊢ w → NL Σ [ y ∘ ((B ⊗ x) ⊗ z) ] ⊢ w
Bₑ′ [] f = Bₑ f
Bₑ′ (_ ⊗> Σ) f = r⇒⊗ (Bₑ′ Σ (r⊗⇒ f))
Bₑ′ (_ ∘> Σ) f = r⇨∘ (Bₑ′ Σ (r∘⇨ f))
Bₑ′ (Σ <⊗ _) f = r⇐⊗ (Bₑ′ Σ (r⊗⇐ f))
Bₑ′ (Σ <∘ _) f = r⇦∘ (Bₑ′ Σ (r∘⇦ f))

Cᵢ′ : ∀ (Σ : Context +) {x y z w} → NL Σ [ x ∘ ((C ⊗ y) ⊗ z) ] ⊢ w → NL Σ [ (x ∘ y) ⊗ z ] ⊢ w
Cᵢ′ [] f = Cᵢ f
Cᵢ′ (_ ⊗> Σ) f = r⇒⊗ (Cᵢ′ Σ (r⊗⇒ f))
Cᵢ′ (_ ∘> Σ) f = r⇨∘ (Cᵢ′ Σ (r∘⇨ f))
Cᵢ′ (Σ <⊗ _) f = r⇐⊗ (Cᵢ′ Σ (r⊗⇐ f))
Cᵢ′ (Σ <∘ _) f = r⇦∘ (Cᵢ′ Σ (r∘⇦ f))

Cₑ′ : ∀ (Σ : Context +) {x y z w} → NL Σ [ (x ∘ y) ⊗ z ] ⊢ w → NL Σ [ x ∘ ((C ⊗ y) ⊗ z) ] ⊢ w
Cₑ′ [] f = Cₑ f
Cₑ′ (_ ⊗> Σ) f = r⇒⊗ (Cₑ′ Σ (r⊗⇒ f))
Cₑ′ (_ ∘> Σ) f = r⇨∘ (Cₑ′ Σ (r∘⇨ f))
Cₑ′ (Σ <⊗ _) f = r⇐⊗ (Cₑ′ Σ (r⊗⇐ f))
Cₑ′ (Σ <∘ _) f = r⇦∘ (Cₑ′ Σ (r∘⇦ f))
