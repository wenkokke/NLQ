------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Level        renaming (suc to lsuc)
open import Data.Fin     using (Fin; suc; zero)
open import Data.List    using (List; map; _++_; _∷_; [])
open import Data.Product using (_×_; _,_; uncurry′)


module Logic.Intuitionistic.Unrestricted.Agda.Environment {ℓ} where


open import Logic.Index hiding (exchange)


infixr 5 _∷_


data Env : List (Set ℓ) → Set (lsuc ℓ) where
  []   : Env []
  _∷_ : {A : Set ℓ} {Γ : List (Set ℓ)} → A → Env Γ → Env (A ∷ Γ)


private
  module Internal {a} {A : Set a} {f : A → Set ℓ} where


    lookup : ∀ {Γ} (e : Env (map f Γ)) (i : Fin _) → f (Γ ‼ i)
    lookup {Γ =    []} [] ()
    lookup {Γ = _ ∷ Γ} (x ∷ _)  zero   = x
    lookup {Γ = _ ∷ Γ} (_ ∷ e) (suc i) = lookup e i


    split : ∀ {Γ₁ Γ₂} → Env (map f (Γ₁ ++ Γ₂)) → Env (map f Γ₁) × Env (map f Γ₂)
    split {Γ₁ = []}      {Γ₂ = Γ₂}     e  = ([] , e)
    split {Γ₁ = _ ∷ Γ₁} {Γ₂ = Γ₂} (x ∷ e) with split {Γ₁ = Γ₁} {Γ₂ = Γ₂} e
    split {Γ₁ = _ ∷ Γ₁} {Γ₂ = Γ₂} (x ∷ e) | (e₁ , e₂) = (x ∷ e₁) , e₂


    split_into_ : ∀ {r} {R : Set r} {Γ₁ Γ₂}
                  → Env (map f (Γ₁ ++ Γ₂)) → (Env (map f Γ₁) → Env (map f Γ₂) → R) → R
    split_into_ e f = uncurry′ f (split e)


    exchange : ∀ Γ₁ Γ₂ Γ₃ Γ₄
             → Env (map f ((Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄)))
             → Env (map f ((Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄)))
    exchange (_ ∷ Γ₁) Γ₂      Γ₃  Γ₄ (x ∷ e) = x ∷ exchange Γ₁ Γ₂ Γ₃ Γ₄ e
    exchange      []  Γ₂      []  Γ₄      e  = e
    exchange      []  Γ₂ (_ ∷ Γ₃) Γ₄ (x ∷ e) = insert Γ₂ (Γ₃ ++ Γ₄) x (exchange [] Γ₂ Γ₃ Γ₄ e)
      where
        insert : ∀ {A} Γ₁ Γ₂ → f A → Env (map f (Γ₁ ++ Γ₂)) → Env (map f (Γ₁ ++ (A ∷ Γ₂)))
        insert      []  Γ₂ x      e  = x ∷ e
        insert (_ ∷ Γ₁) Γ₂ x (y ∷ e) = y ∷ insert Γ₁ Γ₂ x e


open Internal public
