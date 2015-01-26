open import Level        using (suc)
open import Function     using (_∘_)
open import Data.List    using (List; map) renaming (_∷_ to _,_)
open import Data.Product using (_×_; proj₁; proj₂; _,_; uncurry′)
open import Data.Sum     using (_⊎_; [_,_])


module Logic.Classical.Unrestricted.LambdaCMinus.ToAgda {ℓ₁ ℓ₂} (Univ : Set ℓ₁) (⟦_⟧ᵁ : Univ → Set ℓ₂) (R : Set ℓ₂) where


open import Logic.Type Univ renaming (_⇚_ to _-_)
open import Logic.Intuitionistic.Unrestricted.Agda.Environment
open import Logic.Classical.Judgement Univ
open import Logic.Classical.Judgement.ToAgda Univ ⟦_⟧ᵁ R
open import Logic.Classical.Unrestricted.LambdaCMinus.Base Univ


[_] : ∀ {J} → λC⁻ J → λΠ J
[ ax                   ] (x , ·) (k , _) = k x
[ ⇒ᵢ               f   ]      e  (k , r) = k (λ k x → [ f ] (x , e) (k , r))
[ ⇒ₑ               f g ]      e  (k , r) = split e into λ e₁ e₂
                                         → [ f ] e₁ ((λ x → [ g ] e₂ (x k , r)) , r)
[ raa              f   ]      e  (k , r) = [ f ] e (     k , r )
[ ⇒ₑᵏ              α f ]      e       r  = [ f ] e (lookup r α , r)
[ -ᵢ               f g ]      e  (k , r) = split e into λ e₁ e₂
                                         → [ f ] e₁ ((λ x → k ((λ y → [ g ] (y , e₂) r) , x)) , r) 
[ -ₑ               f g ]      e  (k , r) = split e into λ e₁ e₂
                                         → [ f ] e₁ ((λ {(x , y) → [ g ] (y , e₂) (k , (x , r))}) , r)
[ ⊗ᵢ               f g ]      e  (k , r) = split e into λ e₁ e₂
                                         → [ f ] e₁ ((λ x → [ g ] e₂ ((λ y → k (λ l → l (x , y))) , r)) , r)
[ ⊗ₑ               f g ]      e  (k , r) = split e into λ e₁ e₂
                                         → [ f ] e₁ ((λ l → l (λ {(x , y) → [ g ] (x , (y , e₂)) ((λ z → k z) , r)})) , r)
[ eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ f   ]      e  (k , r) = [ f ] (exchange Γ₁ Γ₃ Γ₂ Γ₄ e) (k , r)
[ cᴸ₁              f   ] (x , e) (k , r) = [ f ] (x , (x , e)) (k , r)
[ wᴸ₁              f   ] (x , e) (k , r) = [ f ]           e   (k , r)

