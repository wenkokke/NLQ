------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Rewrites proofs in the structural axiomatisation of LG to proofs in
-- the algebraic axiomatisation of LG with admissible transitivity.
--
-- Every proof in `LG` maps to *exactly one* proof in `RM`, namely a
-- proof for the judgement obtained by deflating all structures (using
-- `⟦_⟧` below) and removing focus.
--
-- Exports translation as `Str→Alg`.
------------------------------------------------------------------------


open import Function using (id; _∘_)


module Logic.LG.ToResMon {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.LG.Type                Atom
open import Logic.LG.Structure.Polarised Atom as SS
open import Logic.LG.Sequent           Atom as SJ
open import Logic.LG.Base                Atom as SB renaming (LG_ to Str_)
open import Logic.LG.ResMon.Sequent    Atom as AJ
open import Logic.LG.ResMon.Base         Atom as AB renaming (LG_ to Alg_)


infix 5 ↓_


↓_ : ∀ {p} → Structure p → Type
↓ · A · = A
↓ [ X ] = □ (↓ X)
↓ ⟨ X ⟩ = ◇ (↓ X)
↓ ₀   X = ₀ (↓ X)
↓ X   ⁰ = (↓ X) ⁰
↓ ₁   X = ₁ (↓ X)
↓ X   ¹ = (↓ X) ¹
↓ X ⊗ Y = (↓ X) ⊗ (↓ Y)
↓ X ⇚ Y = (↓ X) ⇚ (↓ Y)
↓ X ⇛ Y = (↓ X) ⇛ (↓ Y)
↓ X ⊕ Y = (↓ X) ⊕ (↓ Y)
↓ X ⇒ Y = (↓ X) ⇒ (↓ Y)
↓ X ⇐ Y = (↓ X) ⇐ (↓ Y)



private
  -- Map Sequent between systems
  To : SJ.Sequent → AJ.Sequent
  To (  X  ⊢  Y  ) = ↓ X ⊢ ↓ Y
  To ([ A ]⊢  Y  ) =   A ⊢ ↓ Y
  To (  X  ⊢[ B ]) = ↓ X ⊢   B

  to : ∀ {J} → Str J → Alg (To J)
  to  ax⁺      = ax′
  to  ax⁻      = ax′
  to (⇁   f  ) = to f
  to (↽   f  ) = to f
  to (⇀   f  ) = to f
  to (↼   f  ) = to f
  to (◇L  f  ) = to f
  to (◇R  f  ) = m◇  (to f)
  to (□L  f  ) = m□  (to f)
  to (□R  f  ) = to f
  to (r□◇ f  ) = r□◇ (to f)
  to (r◇□ f  ) = r◇□ (to f)
  to (₀L  f  ) = m₀  (to f)
  to (₀R  f  ) = to f
  to (⁰L  f  ) = m⁰  (to f)
  to (⁰R  f  ) = to f
  to (₁L  f  ) = to f
  to (₁R  f  ) = m₁  (to f)
  to (¹L  f  ) = to f
  to (¹R  f  ) = m¹  (to f)
  to (r⁰₀ f  ) = r⁰₀ (to f)
  to (r₀⁰ f  ) = r₀⁰ (to f)
  to (r¹₁ f  ) = r¹₁ (to f)
  to (r₁¹ f  ) = r₁¹ (to f)
  to (⊗L  f  ) = to f
  to (⊗R  f g) = m⊗  (to f) (to g)
  to (⇒L  f g) = m⇒  (to f) (to g)
  to (⇒R  f  ) = to f
  to (⇐L  f g) = m⇐  (to g) (to f)
  to (⇐R  f  ) = to f
  to (r⇒⊗ f  ) = r⇒⊗ (to f)
  to (r⊗⇒ f  ) = r⊗⇒ (to f)
  to (r⇐⊗ f  ) = r⇐⊗ (to f)
  to (r⊗⇐ f  ) = r⊗⇐ (to f)
  to (⊕L  f g) = m⊕  (to f) (to g)
  to (⊕R  f  ) = to f
  to (⇚L  f  ) = to f
  to (⇚R  f g) = m⇚  (to f) (to g)
  to (⇛L  f  ) = to f
  to (⇛R  f g) = m⇛  (to g) (to f)
  to (r⇚⊕ f  ) = r⇚⊕ (to f)
  to (r⊕⇚ f  ) = r⊕⇚ (to f)
  to (r⇛⊕ f  ) = r⇛⊕ (to f)
  to (r⊕⇛ f  ) = r⊕⇛ (to f)
  to (d⇛⇐ f  ) = d⇛⇐ (to f)
  to (d⇛⇒ f  ) = d⇛⇒ (to f)
  to (d⇚⇒ f  ) = d⇚⇒ (to f)
  to (d⇚⇐ f  ) = d⇚⇐ (to f)


Str→Alg : Translation Type Type Str_ Alg_
Str→Alg = record { ⟦_⟧ᵗ = id ; ⟦_⟧ʲ = To ; [_] = to }
