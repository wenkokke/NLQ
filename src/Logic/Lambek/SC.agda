------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


module Logic.Lambek.SC {ℓ} (Univ : Set ℓ) where


open import Logic.Lambek.SC.Judgement          Univ public
open import Logic.Lambek.SC.Base               Univ public
open import Logic.Lambek.SC.EquivalentToResMon Univ public
open import Logic.Lambek.SC.Trans              Univ public
