------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Algebra                    using (module Monoid)
open import Category.Monad             using (module RawMonad)
open import Data.Fin                   using (Fin; suc; zero; #_)
open import Data.Fin.Properties        using (_≟_)
open import Data.List                  using (List; _∷_; []; _++_; length)
open import Data.Maybe                 using (Maybe; just; nothing)
open import Data.Nat                   using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties.Simple using (+-suc)
open import Data.Product               using (_×_; _,_; proj₁; proj₂)
open import Data.Vec                   using (Vec; _∷_; []; lookup)
open import Relation.Nullary           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality


module Logic.Intuitionistic.Unrestricted.Lambda.Untyped.Base where


open import Logic.Index


data Term (n : ℕ) : Set where
  ax : (x : Fin n) → Term n
  ⇒ᵢ : (x : Term (suc n)) → Term n
  ⇒ₑ : (f x : Term n) → Term n
  ⊗ᵢ : (x y : Term n) → Term n
  ⊗ₑ : (x : Term n) (f : Term (suc (suc n))) → Term n


private
  thick : ∀ {n} → (x y : Fin (suc n)) → Maybe (Fin n)
  thick          zero    zero   = nothing
  thick          zero   (suc y) = just y
  thick {zero}  (suc ()) _
  thick {suc n} (suc x)  zero   = just zero
  thick {suc n} (suc x) (suc y) = suc <$> thick x y
    where
      open RawMonad Data.Maybe.monad using (_<$>_)

  raise : ∀ {n} (m : ℕ) → Term n → Term (m + n)
  raise {n} m (ax x)   = ax (Data.Fin.raise m x)
  raise {n} m (⇒ᵢ f)   = ⇒ᵢ (subst Term (+-suc m n) (raise m f))
  raise {n} m (⇒ₑ f g) = ⇒ₑ (raise m f) (raise m g)
  raise {n} m (⊗ᵢ f g) = ⊗ᵢ (raise m f) (raise m g)
  raise {n} m (⊗ₑ f g) = ⊗ₑ (raise m f)
    (subst Term (trans (+-suc m (suc n)) (cong suc (+-suc m n))) (raise m g))

  _[_≔_]′ : ∀ {n} → Term (suc n) → Fin (suc n) → Term n → Term n
  ax x   [ y ≔ e ]′ with thick x y
  ax x   [ y ≔ e ]′ | just x′ = ax x′
  ax x   [ y ≔ e ]′ | nothing = e
  ⇒ᵢ f   [ y ≔ e ]′ = ⇒ᵢ (f [ suc y ≔ raise 1 e ]′)
  ⇒ₑ f g [ y ≔ e ]′ = ⇒ₑ (f [ y ≔ e ]′) (g [ y ≔ e ]′)
  ⊗ᵢ f g [ y ≔ e ]′ = ⊗ᵢ (f [ y ≔ e ]′) (g [ y ≔ e ]′)
  ⊗ₑ f g [ y ≔ e ]′ = ⊗ₑ (f [ y ≔ e ]′) (g [ suc (suc y) ≔ raise 2 e ]′)

{-# TERMINATING #-}
norm : ∀ {n} → Term n → Term n
norm (ax x)          = ax x
norm (⇒ᵢ f)          = ⇒ᵢ f
norm (⇒ₑ (⇒ᵢ f) g)   = norm (f [ zero ≔ norm g ]′)
norm (⇒ₑ f g)        = ⇒ₑ (norm f) (norm g)
norm (⊗ᵢ f g)        = ⊗ᵢ f g
norm (⊗ₑ (⊗ᵢ x y) g) = norm (g [ zero ≔ raise 1 (norm x) ]′ [ zero ≔ norm y ]′)
norm (⊗ₑ f g)        = ⊗ₑ (norm f) (norm g)

_[_≔_] : ∀ {n m} → Term (suc n) → Fin (suc n) → Term m → Term (n + m)
_[_≔_] {n} {m} (ax y) x e with thick x y
_[_≔_] {_} {m} (ax y) x e | just x′ = ax (Data.Fin.inject+ m x′)
_[_≔_] {n} {_} (ax y) x e | nothing = raise n e
⇒ᵢ f   [ x ≔ e ] = ⇒ᵢ (f [ suc x ≔ e ])
⇒ₑ f g [ x ≔ e ] = ⇒ₑ (f [ x ≔ e ]) (g [ x ≔ e ])
⊗ᵢ f g [ x ≔ e ] = ⊗ᵢ (f [ x ≔ e ]) (g [ x ≔ e ])
⊗ₑ f g [ x ≔ e ] = ⊗ₑ (f [ x ≔ e ]) (g [ suc (suc x) ≔ e ])
