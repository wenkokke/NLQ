------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambekGrishin.Trans {ℓ} (Univ : Set ℓ) where


open import Logic.Polarity
open import Logic.Classical.Ordered.LambekGrishin.Type                Univ
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Univ
open import Logic.Classical.Ordered.LambekGrishin.Judgement           Univ
open import Logic.Classical.Ordered.LambekGrishin.Base                Univ
open import Logic.Classical.Ordered.LambekGrishin.EquivalentToResMon  Univ
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Base         Univ renaming (LG_ to RM_)
open import Logic.Classical.Ordered.LambekGrishin.ResMon.Trans        Univ as RM using ()


trans′ : ∀ {X A Y} → LG X ⊢[ A ] → LG [ A ]⊢ Y → LG X ⊢ Y
trans′ f g = reinflate⁻ (reinflate⁺ (from (RM.trans′ (to f) (to g))))
