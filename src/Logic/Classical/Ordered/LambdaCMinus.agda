------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambdaCMinus {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambdaCMinus.Type       Univ public
open import Logic.Classical.Ordered.LambdaCMinus.Structure  Univ public
open import Logic.Classical.Ordered.LambdaCMinus.Judgement  Univ public
open import Logic.Classical.Ordered.LambdaCMinus.Base       Univ public
open import Logic.Classical.Ordered.LambdaCMinus.ToLinear   Univ public
