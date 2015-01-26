open import Level        using (suc)
open import Function     using (_∘_)
open import Data.List    using (List; map) renaming (_∷_ to _,_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Classical.Unrestricted.LambdaCMinus.Indexed.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) (R : Set ℓ₂) where


open import Logic.Type Univ renaming (_⇚_ to _-_)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open import Logic.Classical.Judgement Univ
open import Logic.Classical.Judgement.ToAgda Univ ⟦_⟧ᵁ R
open import Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Base Univ


[_] : ∀ {J} → λC⁻ J → λΠ J
[ ax  x   ] e (k , _) = k (lookup e x)
[ ⇒ᵢ  f   ] e (k , r) = k (λ k x → [ f ] (x , e) (k , r))
[ ⇒ₑ  f g ] e (k , r) = [ f ] e ((λ x → [ g ] e (x k , r)) , r)
[ raa f   ] e (k , r) = [ f ] e (     k , r )
[ ⇒ₑᵏ α f ] e      r  = [ f ] e (lookup r α , r)
[ -ᵢ  f g ] e (k , r) = [ f ] e ((λ x → k ((λ y → [ g ] (y , e) r) , x)) , r) 
[ -ₑ  f g ] e (k , r) = [ f ] e ((λ {(x , y) → [ g ] (y , e) (k , (x , r))}) , r)
[ ⊗ᵢ  f g ] e (k , r) = [ f ] e ((λ x → [ g ] e ((λ y → k (λ l → l (x , y))) , r)) , r)
[ ⊗ₑ  f g ] e (k , r) = [ f ] e ((λ l → l (λ {(x , y) → [ g ] (x , (y , e)) (k , r)})) , r)
