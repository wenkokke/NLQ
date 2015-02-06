------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.List using (List)


module Logic.Classical.Ordered.LambdaCMinus.Judgement {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambdaCMinus.Type      Univ
open import Logic.Classical.Ordered.LambdaCMinus.Structure Univ


infix 3 _⊢_ _⊢[_]_


data Judgement : Set ℓ where
  _⊢_    : Structure →        List Type → Judgement
  _⊢[_]_ : Structure → Type → List Type → Judgement


anta : Judgement → Structure
anta (Γ ⊢      _) = Γ
anta (Γ ⊢[ _ ] _) = Γ

succ : Judgement → List Type
succ (_ ⊢      Δ) = Δ
succ (_ ⊢[ _ ] Δ) = Δ
