------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.Experimental.EquivalentToResMon {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.Experimental.Type                Univ
open import Logic.Classical.Ordered.Experimental.Structure.Polarised Univ
open import Logic.Classical.Ordered.Experimental.Judgement           Univ as SJ
open import Logic.Classical.Ordered.Experimental.Base                Univ as SB renaming (EXP_ to Str_)
open import Logic.Classical.Ordered.Experimental.ResMon.Judgement    Univ as AJ
open import Logic.Classical.Ordered.Experimental.ResMon.Base         Univ as AB renaming (EXP_ to Alg_)
open import Logic.Classical.Ordered.Experimental.ResMon.Trans        Univ as AT using ()



-- Deflate a `Structure` into a `Type`
⟦_⟧ : ∀ {p} → Structure p → Type
⟦ · A · ⟧ = A
⟦ [ X ] ⟧ = □ ⟦ X ⟧
⟦ ⟨ X ⟩ ⟧ = ◇ ⟦ X ⟧
⟦  ₀ X  ⟧ = ₀ ⟦ X ⟧
⟦  X ⁰  ⟧ = ⟦ X ⟧ ⁰
⟦  ₁ X  ⟧ = ₁ ⟦ X ⟧
⟦  X ¹  ⟧ = ⟦ X ⟧ ¹
⟦ X ⊗ Y ⟧ = ⟦ X ⟧ ⊗ ⟦ Y ⟧
⟦ X ⇚ Y ⟧ = ⟦ X ⟧ ⇚ ⟦ Y ⟧
⟦ X ⇛ Y ⟧ = ⟦ X ⟧ ⇛ ⟦ Y ⟧
⟦ X ⊕ Y ⟧ = ⟦ X ⟧ ⊕ ⟦ Y ⟧
⟦ X ⇒ Y ⟧ = ⟦ X ⟧ ⇒ ⟦ Y ⟧
⟦ X ⇐ Y ⟧ = ⟦ X ⟧ ⇐ ⟦ Y ⟧


-- Map Judgement between systems
To : SJ.Judgement → AJ.Judgement
To (  X  ⊢  Y  ) = ⟦ X ⟧ ⊢ ⟦ Y ⟧
To ([ A ]⊢  Y  ) =   A   ⊢ ⟦ Y ⟧
To (  X  ⊢[ B ]) = ⟦ X ⟧ ⊢   B

to : ∀ {J} → Str J → Alg (To J)
to  ax⁺      = ax′
to  ax⁻      = ax′
to (⇁   f  ) = to f
to (↽   f  ) = to f
to (⇀   f  ) = to f
to (↼   f  ) = to f
to (◇ᴸ  f  ) = to f
to (◇ᴿ  f  ) = m◇  (to f)
to (□ᴸ  f  ) = m□  (to f)
to (□ᴿ  f  ) = to f
to (₀ᴸ  f  ) = m₀  (to f)
to (₀ᴿ  f  ) = to f
to (⁰ᴸ  f  ) = m⁰  (to f)
to (⁰ᴿ  f  ) = to f
to (₁ᴸ  f  ) = to f
to (₁ᴿ  f  ) = m₁  (to f)
to (¹ᴸ  f  ) = to f
to (¹ᴿ  f  ) = m¹  (to f)
to (r⁰₀ f  ) = r⁰₀ (to f)
to (r₀⁰ f  ) = r₀⁰ (to f)
to (r¹₁ f  ) = r¹₁ (to f)
to (r₁¹ f  ) = r₁¹ (to f)
to (⊗ᴸ  f  ) = to f
to (⊗ᴿ  f g) = m⊗  (to f) (to g)
to (⇒ᴸ  f g) = m⇒  (to f) (to g)
to (⇒ᴿ  f  ) = to f
to (⇐ᴸ  f g) = m⇐  (to g) (to f)
to (⇐ᴿ  f  ) = to f
to (r⇒⊗ f  ) = r⇒⊗ (to f)
to (r⊗⇒ f  ) = r⊗⇒ (to f)
to (r⇐⊗ f  ) = r⇐⊗ (to f)
to (r⊗⇐ f  ) = r⊗⇐ (to f)
to (⊕ᴸ  f g) = m⊕  (to f) (to g)
to (⊕ᴿ  f  ) = to f
to (⇚ᴸ  f  ) = to f
to (⇚ᴿ  f g) = m⇚  (to f) (to g)
to (⇛ᴸ  f  ) = to f
to (⇛ᴿ  f g) = m⇛  (to g) (to f)
to (r⇚⊕ f  ) = r⇚⊕ (to f)
to (r⊕⇚ f  ) = r⊕⇚ (to f)
to (r⇛⊕ f  ) = r⇛⊕ (to f)
to (r⊕⇛ f  ) = r⊕⇛ (to f)
