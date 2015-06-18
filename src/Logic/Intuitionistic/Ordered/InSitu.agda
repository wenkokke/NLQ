------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Intuitionistic.Ordered.InSitu {ℓ} (Atom : Set ℓ) where


open import Logic.Intuitionistic.Ordered.InSitu.Type                   Atom public
open import Logic.Intuitionistic.Ordered.InSitu.Type.Context.Polarised Atom public
open import Logic.Intuitionistic.Ordered.InSitu.Judgement              Atom public
open import Logic.Intuitionistic.Ordered.InSitu.Base                   Atom public
