------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Data.String renaming (String to Name)


module Logic.Classical.Unrestricted.LambdaCMinus.Named.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Unrestricted.LambdaCMinus.Type Univ


infixr 9 _$_ _$ᴷ_
infixr 5 λ⟨_∶_⟩→_ λ⟨_,_∶_⟩→_

data Term : Set ℓ where

  v            : (x : Name)                         → Term

  _$_          : (f x : Term)                       → Term

  λ⟨_∶_⟩→_     : (x : Name) (t : Type) (b : Term)   → Term

  _$ᴷ_         : (k : Name) (x : Term)              → Term

  C⁻[λ⟨_∶_⟩→_] : (k : Name) (t : Type) (b : Term)   → Term

  ⟨_,_⟩        : (x y : Term)                       → Term

  λ⟨_,_∶_⟩→_   : (x y : Name) (t : Type) (b : Term) → Term
