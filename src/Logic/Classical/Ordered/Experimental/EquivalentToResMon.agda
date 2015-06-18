------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.Experimental.EquivalentToResMon {ℓ} (Atom : Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.Classical.Ordered.Experimental.Type                Atom
open import Logic.Classical.Ordered.Experimental.Structure.Polarised Atom
open import Logic.Classical.Ordered.Experimental.Judgement           Atom as SJ
open import Logic.Classical.Ordered.Experimental.Base                Atom as SB renaming (EXP_ to Str_)
open import Logic.Classical.Ordered.Experimental.ResMon.Judgement    Atom as AJ
open import Logic.Classical.Ordered.Experimental.ResMon.Base         Atom as AB renaming (EXP_ to Alg_)
open import Logic.Classical.Ordered.Experimental.ResMon.Trans        Atom as AT using ()
open import Logic.Classical.Ordered.Experimental.ToResMon            Atom using (↓_; Str→Alg)
