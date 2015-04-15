------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Intuitionistic.Ordered.NLCL {ℓ} (Univ : Set ℓ) (I L R : Univ) where


open import Logic.Polarity
open import Logic.Intuitionistic.Ordered.NLCL.Type                   Univ
open import Logic.Intuitionistic.Ordered.NLCL.Type.Context.Polarised Univ
open import Logic.Intuitionistic.Ordered.NLCL.Judgement              Univ
open import Logic.Intuitionistic.Ordered.NLCL.Base                   Univ
