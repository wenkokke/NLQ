------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Intuitionistic.Structure.Context {ℓ} (Univ : Set ℓ) where


open import Logic.Intuitionistic.Type                       Univ as T hiding (module DecEq)
open import Logic.Intuitionistic.Structure Univ as S


infixr 30 _<,_ _,>_

data ListContext : Set ℓ where
  []   : ListContext
  _<,_ : ListContext → List Type   → ListContext
  _,>_ : Type        → ListContext → ListContext


_<,_-injective : ∀ {X Y Z W} → X <, Z ≡ Y <, W → X ≡ Y × Z ≡ W
_<,_-injective refl = refl , refl

_,>_-injective : ∀ {A B X Y} → A ,> X ≡ B ,> Y → A ≡ B × X ≡ Y
_,>_-injective refl = refl , refl


module Simple where

  infix 50 _[_]

  _[_] : ListContext → List Type → List Type
  []       [ Z ] = Z
  (X <, Y) [ Z ] = X [ Z ] ++ Y
  (A ,> Y) [ Z ] = A , Y [ Z ]
