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
open import Logic.Classical.Ordered.Experimental.ToResMon            Univ using (↓_; Str→Alg)
