------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Level using (suc)
open import Data.List using (List; _∷_; []; _++_)
open import Data.Product using (_×_; _,_)
open import Logic.Reification

module Logic.Intuitionistic.Agda.Base
  {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (Univ→Set : Reify Univ (Set ℓ₂)) where


open import Logic.Intuitionistic.Judgement        Univ
open import Logic.Intuitionistic.Judgement.ToAgda Univ Univ→Set


infix 1 λΠ_

λΠ_ : Judgement → Set ℓ₂
λΠ J = ⟦ J ⟧
