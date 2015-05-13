------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Intuitionistic.Ordered.InSitu {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Ordered.InSitu.Type                   Univ public
open import Logic.Intuitionistic.Ordered.InSitu.Type.Context.Polarised Univ public
open import Logic.Intuitionistic.Ordered.InSitu.Judgement              Univ public
open import Logic.Intuitionistic.Ordered.InSitu.Base                   Univ public
