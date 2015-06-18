------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level        using (suc)
open import Function     using (_∘_) renaming (id to λΠ_)
open import Data.List    using (List; _∷_; map)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Classical.Unrestricted.LambdaCMinus.Indexed.ToAgda {ℓ₁ ℓ₂} (Atom : Set ℓ₁) (⟦_⟧ᵁ : Atom → Set ℓ₂) (R : Set ℓ₂) where


open import Logic.Translation
open import Logic.Classical.Unrestricted.LambdaCMinus.Type         Atom
open import Logic.Classical.Unrestricted.LambdaCMinus.Judgement    Atom
open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Base Atom
open import Logic.Classical.Unrestricted.LambdaCMinus.ToAgda       Atom ⟦_⟧ᵁ R as E hiding (Un→Agda)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment


private
  open Translation E.Un→Agda using (⟦_⟧ᵀ; ⟦_⟧ᴶ)

  [_] : ∀ {J} → λC⁻ J → ⟦ J ⟧ᴶ
  [ ax  x   ] e (k ∷ _) = k (lookup e x)
  [ ⇒ᵢ  f   ] e (k ∷ r) = k (λ k x → [ f ] (x ∷ e) (k ∷ r))
  [ ⇒ₑ  f g ] e (k ∷ r) = [ f ] e ((λ x → [ g ] e (x k ∷ r)) ∷ r)
  [ raa f   ] e (k ∷ r) = [ f ] e (     k ∷ r )
  [ ⇒ₑᵏ α f ] e      r  = [ f ] e (lookup r α ∷ r)
  [ -ᵢ  f g ] e (k ∷ r) = [ f ] e ((λ x → k ((λ y → [ g ] (y ∷ e) r) , x)) ∷ r)
  [ -ₑ  f g ] e (k ∷ r) = [ f ] e ((λ {(x , y) → [ g ] (y ∷ e) (k ∷ (x ∷ r))}) ∷ r)
  [ ⊗ᵢ  f g ] e (k ∷ r) = [ f ] e ((λ x → [ g ] e ((λ y → k (λ l → l (x , y))) ∷ r)) ∷ r)
  [ ⊗ₑ  f g ] e (k ∷ r) = [ f ] e ((λ l → l (λ {(x , y) → [ g ] (x ∷ (y ∷ e)) (k ∷ r)})) ∷ r)


Un→Agda : Translation Type (Set ℓ₂) λC⁻_ λΠ_
Un→Agda = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
