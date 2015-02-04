------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level     using (_⊔_)
open import Data.List using (List)


module TypeAndEffect.Judgement {ℓ} (Univ : Set ℓ) where


open import TypeAndEffect.Type Univ


infix 3 _⊢_^_ _^_⊢[_^_]_


data Judgement : Set ℓ where
  _⊢_^_      : List Type →                      List Type → Type → Judgement
  _^_⊢[_^_]_ : List Type → Type → Type → Type → List Type →        Judgement
