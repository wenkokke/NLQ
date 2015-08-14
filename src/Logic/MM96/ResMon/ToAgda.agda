--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- TODO: not yet implemented
--------------------------------------------------------------------------------


open import Function     using (id; _∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)


module Logic.MM96.ResMon.ToAgda
  {a ℓ} (Atom : Set a) (R : Set ℓ) (⟦_⟧ᴬ : Atom → Set ℓ) where


open import Logic.Polarity
open import Logic.Translation
open import Logic.MM96.Type             Atom
open import Logic.MM96.ResMon.Judgement Atom
open import Logic.MM96.ResMon.Base      Atom
