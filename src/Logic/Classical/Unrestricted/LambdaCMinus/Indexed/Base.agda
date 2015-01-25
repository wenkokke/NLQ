open import Algebra                               using (module Monoid)
open import Function                              using (id; _∘_)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List                             using (List; _++_) renaming ([] to ·; _∷_ to _,_)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable            using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

module Logic.Classical.Unrestricted.LambdaCMinus.Indexed.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Type                Univ  renaming (_⇛_ to _-_)
open import Logic.Index          {ℓ} {Type} renaming (lookup to _‼_)
open import Logic.Classical.Judgement Univ
open Monoid (Data.List.monoid Type) using (identity; assoc)


infix 1 λC⁻_

data λC⁻_ : Judgement → Set ℓ where

  ax   : ∀ {Γ Δ} (x : Fin _)
       → λC⁻     Γ ⊢[ Γ ‼ x ]     Δ

  ⇒ᵢ   : ∀ {Γ A B Δ}
       → λC⁻ A , Γ ⊢[     B ]     Δ
       → λC⁻     Γ ⊢[ A ⇒ B ]     Δ

  ⇒ₑ   : ∀ {Γ A B Δ}
       → λC⁻     Γ ⊢[ A ⇒ B ]     Δ
       → λC⁻     Γ ⊢[ A     ]     Δ
       → λC⁻     Γ ⊢[     B ]     Δ

  raa  : ∀ {Γ A Δ}
       → λC⁻     Γ ⊢          A , Δ
       → λC⁻     Γ ⊢[ A     ]     Δ

  ⇒ₑᵏ  : ∀ {Γ Δ} (α : Fin _)
       → λC⁻     Γ ⊢[ Δ ‼ α ]     Δ
       → λC⁻     Γ ⊢              Δ

  -ᵢ   : ∀ {Γ A B Δ}
       → λC⁻     Γ ⊢[ A     ]     Δ
       → λC⁻ B , Γ ⊢              Δ
       → λC⁻     Γ ⊢[ A - B ]     Δ

  -ₑ   : ∀ {Γ A B C Δ}
       → λC⁻     Γ ⊢[ A - B ]     Δ
       → λC⁻ A , Γ ⊢[ C     ] B , Δ
       → λC⁻     Γ ⊢[ C     ]     Δ

  ⊗ᵢ   : ∀ {Γ A B Δ}
       → λC⁻ Γ ⊢[ A     ] Δ
       → λC⁻ Γ ⊢[     B ] Δ
       → λC⁻ Γ ⊢[ A ⊗ B ] Δ

  ⊗ₑ   : ∀ {Γ A B C Δ}
       → λC⁻          Γ  ⊢[ A ⊗ B ] Δ
       → λC⁻ A , (B , Γ) ⊢[ C     ] Δ
       → λC⁻          Γ  ⊢[ C     ] Δ


-- Proof: eᴸ and eᴿ show that the structural rules of left and right
-- exchange are implicit in the axiomatisation that we've chosen.
mutual
  eᴸ   : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) {A Δ}
       → λC⁻ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢[ A ] Δ
       → λC⁻ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢[ A ] Δ
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (ax  x)   with (exchange Γ₁ Γ₂ Γ₃ Γ₄ x)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (ax  x)   | y , p rewrite p = ax y
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⇒ᵢ  f)   = ⇒ᵢ  (eᴸ  (_ , Γ₁) Γ₂ Γ₃ Γ₄ f)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⇒ₑ  f g) = ⇒ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ            Γ₁   Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (raa f)   = raa (eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ f)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (-ᵢ  f g) = -ᵢ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ′      (_ , Γ₁)  Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (-ₑ  f g) = -ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ       (_ , Γ₁)  Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⊗ᵢ  f g) = ⊗ᵢ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ            Γ₁   Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⊗ₑ  f g) = ⊗ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ  (_ , (_ , Γ₁)) Γ₂ Γ₃ Γ₄ g)

  eᴸ′  : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) {Δ}
       → λC⁻ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢      Δ
       → λC⁻ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢      Δ
  eᴸ′  Γ₁ Γ₂ Γ₃ Γ₄ (⇒ₑᵏ α f) = ⇒ₑᵏ α (eᴸ Γ₁ Γ₂ Γ₃ Γ₄ f)

mutual
  eᴿ   : ∀ {Γ A} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → λC⁻ Γ ⊢[ A ] (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → λC⁻ Γ ⊢[ A ] (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (ax  x)   = ax x
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇒ᵢ  f)   = ⇒ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑ  f g) = ⇒ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (raa f)   = raa (eᴿ′ (_ , Δ₁) Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ᵢ  f g) = -ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ′      Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ₑ  f g) = -ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ  (_ , Δ₁) Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⊗ᵢ  f g) = ⊗ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⊗ₑ  f g) = ⊗ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  
  eᴿ′  : ∀ {Γ} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → λC⁻ Γ ⊢      (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → λC⁻ Γ ⊢      (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑᵏ α f) with (exchange Δ₁ Δ₂ Δ₃ Δ₄ α)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑᵏ α f) | β , p rewrite p = ⇒ₑᵏ β (eᴿ Δ₁ Δ₂ Δ₃ Δ₄ f)


-- Lemma: weaker versions of eᴸ and eᴿ which only swap the first two
-- (or three) elements are often useful.
eᴸ₁  : ∀ {Γ A B C Δ}
     → λC⁻ B , (A , Γ) ⊢[ C ] Δ
     → λC⁻ A , (B , Γ) ⊢[ C ] Δ
eᴸ₁  = eᴸ · (_ , ·) (_ , ·) _

eᴸ₁′ : ∀ {Γ A B Δ}
     → λC⁻ B , (A , Γ) ⊢      Δ
     → λC⁻ A , (B , Γ) ⊢      Δ
eᴸ₁′ = eᴸ′ · (_ , ·) (_ , ·) _

eᴸ₂  : ∀ {Γ A B C D Δ}
     → λC⁻ C , (A , (B , Γ)) ⊢[ D ] Δ
     → λC⁻ A , (B , (C , Γ)) ⊢[ D ] Δ
eᴸ₂  = eᴸ · (_ , (_ , ·)) (_ , ·) _

eᴿ₁  : ∀ {Γ A B C Δ}
     → λC⁻ Γ ⊢[ A ] C , (B , Δ)
     → λC⁻ Γ ⊢[ A ] B , (C , Δ)
eᴿ₁  = eᴿ · (_ , ·) (_ , ·) _

eᴿ₁′ : ∀ {Γ B C Δ}
     → λC⁻ Γ ⊢      C , (B , Δ)
     → λC⁻ Γ ⊢      B , (C , Δ)
eᴿ₁′ = eᴿ′ · (_ , ·) (_ , ·) _


-- Lemma: weaker version of eᴸ and eᴿ which only swap two contexts,
-- without allowing them to be embedded in further contexts are often
-- useful as well.
sᴸ  : ∀ (Γ₁ Γ₂ : List Type) {A Δ} → λC⁻ Γ₂ ++ Γ₁ ⊢[ A ] Δ → λC⁻ Γ₁ ++ Γ₂ ⊢[ A ] Δ
sᴸ  ·  Γ₂ {A} {Δ} = subst  (λ Γ → λC⁻ Γ ⊢[ A ] Δ) (     proj₂ identity Γ₂ )
sᴸ  Γ₁ ·  {A} {Δ} = subst  (λ Γ → λC⁻ Γ ⊢[ A ] Δ) (sym (proj₂ identity Γ₁))
sᴸ  Γ₁ Γ₂ {A} {Δ} = subst₂ (λ Γ₁′ Γ₂′ → λC⁻ Γ₂ ++ Γ₁′ ⊢[ A ] Δ → λC⁻ Γ₁ ++ Γ₂′ ⊢[ A ] Δ) (proj₂ identity Γ₁) (proj₂ identity Γ₂) (eᴸ  · Γ₁ Γ₂ ·)

sᴸ′ : ∀ (Γ₁ Γ₂ : List Type) {Δ} → λC⁻ Γ₂ ++ Γ₁ ⊢ Δ → λC⁻ Γ₁ ++ Γ₂ ⊢ Δ
sᴸ′ ·  Γ₂ {Δ} = subst  (λ Γ → λC⁻ Γ ⊢ Δ) (     proj₂ identity Γ₂ )
sᴸ′ Γ₁ ·  {Δ} = subst  (λ Γ → λC⁻ Γ ⊢ Δ) (sym (proj₂ identity Γ₁))
sᴸ′ Γ₁ Γ₂ {Δ} = subst₂ (λ Γ₁′ Γ₂′ → λC⁻ Γ₂ ++ Γ₁′ ⊢ Δ → λC⁻ Γ₁ ++ Γ₂′ ⊢ Δ) (proj₂ identity Γ₁) (proj₂ identity Γ₂) (eᴸ′ · Γ₁ Γ₂ ·)

sᴿ  : ∀ {Γ A} (Δ₁ Δ₂ : List Type) → λC⁻ Γ ⊢[ A ] Δ₂ ++ Δ₁ → λC⁻ Γ ⊢[ A ] Δ₁ ++ Δ₂
sᴿ  ·  Δ₂ = subst  (λ Δ → λC⁻ _ ⊢[ _ ] Δ) (     proj₂ identity Δ₂ )
sᴿ  Δ₁ ·  = subst  (λ Δ → λC⁻ _ ⊢[ _ ] Δ) (sym (proj₂ identity Δ₁))
sᴿ  Δ₁ Δ₂ = subst₂ (λ Δ₁′ Δ₂′ → λC⁻ _ ⊢[ _ ] Δ₂ ++ Δ₁′ → λC⁻ _ ⊢[ _ ] Δ₁ ++ Δ₂′) (proj₂ identity Δ₁) (proj₂ identity Δ₂) (eᴿ  · Δ₁ Δ₂ ·)

sᴿ′ : ∀ {Γ} (Δ₁ Δ₂ : List Type) → λC⁻ Γ ⊢ Δ₂ ++ Δ₁ → λC⁻ Γ ⊢ Δ₁ ++ Δ₂
sᴿ′ ·  Δ₂ = subst  (λ Δ → λC⁻ _ ⊢ Δ) (     proj₂ identity Δ₂ )
sᴿ′ Δ₁ ·  = subst  (λ Δ → λC⁻ _ ⊢ Δ) (sym (proj₂ identity Δ₁))
sᴿ′ Δ₁ Δ₂ = subst₂ (λ Δ₁′ Δ₂′ → λC⁻ _ ⊢ Δ₂ ++ Δ₁′ → λC⁻ _ ⊢ Δ₁ ++ Δ₂′) (proj₂ identity Δ₁) (proj₂ identity Δ₂) (eᴿ′ · Δ₁ Δ₂ ·)


-- Lemma: weaker versions of weakning for which simply allows for the
-- addition of one unused premise can easily be induced from the
-- axioms.
mutual
  wᴸ₁  : ∀ {Γ A B Δ}
       → λC⁻     Γ ⊢[ B ] Δ
       → λC⁻ A , Γ ⊢[ B ] Δ
  wᴸ₁ (ax  x)   = ax (suc x)
  wᴸ₁ (⇒ᵢ  f)   = ⇒ᵢ  (eᴸ₁ (wᴸ₁ f))
  wᴸ₁ (⇒ₑ  f g) = ⇒ₑ  (wᴸ₁  f) (wᴸ₁ g)
  wᴸ₁ (raa f)   = raa (wᴸ₁′ f)
  wᴸ₁ (-ᵢ  f g) = -ᵢ  (wᴸ₁  f) (eᴸ₁′ (wᴸ₁′ g))
  wᴸ₁ (-ₑ  f g) = -ₑ  (wᴸ₁  f) (eᴸ₁  (wᴸ₁  g))
  wᴸ₁ (⊗ᵢ  f g) = ⊗ᵢ  (wᴸ₁  f) (wᴸ₁ g)
  wᴸ₁ (⊗ₑ  f g) = ⊗ₑ  (wᴸ₁  f) (eᴸ₂ (wᴸ₁ g))

  wᴸ₁′ : ∀ {Γ A Δ}
       → λC⁻     Γ ⊢      Δ
       → λC⁻ A , Γ ⊢      Δ
  wᴸ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ α (wᴸ₁ f)

mutual
  wᴿ₁  : ∀ {Γ A B Δ}
       → λC⁻ Γ ⊢[ A ]     Δ
       → λC⁻ Γ ⊢[ A ] B , Δ
  wᴿ₁  (ax  x)   = ax x
  wᴿ₁  (⇒ᵢ  f)   = ⇒ᵢ  (wᴿ₁  f)
  wᴿ₁  (⇒ₑ  f g) = ⇒ₑ  (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (raa f)   = raa (eᴿ₁′ (wᴿ₁′ f))
  wᴿ₁  (-ᵢ  f g) = -ᵢ  (wᴿ₁  f) (wᴿ₁′ g)
  wᴿ₁  (-ₑ  f g) = -ₑ  (wᴿ₁  f) (eᴿ₁ (wᴿ₁ g))
  wᴿ₁  (⊗ᵢ  f g) = ⊗ᵢ  (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (⊗ₑ  f g) = ⊗ₑ  (wᴿ₁  f) (wᴿ₁ g)
  
  wᴿ₁′ : ∀ {Γ A Δ}
       → λC⁻ Γ ⊢          Δ
       → λC⁻ Γ ⊢      A , Δ
  wᴿ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ (suc α) (wᴿ₁ f)


-- Proof: weakening follows easily by induction from the simplified
-- versions of weakening proved above.
wᴸ  : ∀ Γ₁ {Γ₂ A Δ}
    → λC⁻       Γ₂ ⊢[ A ] Δ
    → λC⁻ Γ₁ ++ Γ₂ ⊢[ A ] Δ
wᴸ       ·   f = f
wᴸ  (A , Γ₁) f = wᴸ₁  (wᴸ  Γ₁ f)

wᴸ′ : ∀ Γ₁ {Γ₂ Δ}
    → λC⁻       Γ₂ ⊢      Δ
    → λC⁻ Γ₁ ++ Γ₂ ⊢      Δ
wᴸ′      ·   f = f
wᴸ′ (A , Γ₁) f = wᴸ₁′ (wᴸ′ Γ₁ f) 

wᴿ  : ∀ {Γ A} Δ₁ {Δ₂}
    → λC⁻ Γ ⊢[ A ]       Δ₂
    → λC⁻ Γ ⊢[ A ] Δ₁ ++ Δ₂
wᴿ       ·   f = f
wᴿ  (A , Δ₁) f = wᴿ₁  (wᴿ  Δ₁ f)

wᴿ′ : ∀ {Γ} Δ₁ {Δ₂}
    → λC⁻ Γ ⊢       Δ₂
    → λC⁻ Γ ⊢ Δ₁ ++ Δ₂
wᴿ′      ·   f = f
wᴿ′ (A , Δ₁) f = wᴿ₁′ (wᴿ′ Δ₁ f)


-- There are two special versions for the right-hand sided lemmas,
-- |ėᴿ₁| and |ċᴿ₁|, which allow for exchange with and contraction into
-- focused expressions.
ėᴿ₁  : ∀ {Γ A B Δ}
     → λC⁻ Γ ⊢[ A ] B , Δ
     → λC⁻ Γ ⊢[ B ] A , Δ
ėᴿ₁  f = raa (⇒ₑᵏ (# 1) (eᴿ₁ (wᴿ₁ f)))

ċᴿ₁  : ∀ {Γ A Δ}
     → λC⁻ Γ ⊢[ A ] A , Δ
     → λC⁻ Γ ⊢[ A ]     Δ
ċᴿ₁  f = raa (⇒ₑᵏ (# 0) f)


-- Lemma: weaker versions of contraction, which contract two (co-)values of
-- the same type, can easily be derived from the axioms. There is a
-- special version for the right-hand sided lemma, |cᶠ₁|, which allows
-- for contraction into the focused expression.
cᴸ₁  : ∀ {Γ A B Δ}
     → λC⁻ A , (A , Γ) ⊢[ B ] Δ
     → λC⁻      A , Γ  ⊢[ B ] Δ
cᴸ₁  f = ⇒ₑ (⇒ᵢ f) (ax (# 0))

cᴸ₁′ : ∀ {Γ A Δ}
     → λC⁻ A , (A , Γ) ⊢ Δ
     → λC⁻      A , Γ  ⊢ Δ
cᴸ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ α (cᴸ₁ f)

cᴿ₁  : ∀ {Γ A B Δ}
     → λC⁻ Γ ⊢[ A ] B , (B , Δ)
     → λC⁻ Γ ⊢[ A ]      B , Δ
cᴿ₁  f = ėᴿ₁ (ċᴿ₁ (eᴿ₁ (ėᴿ₁ f)))

cᴿ₁′ : ∀ {Γ B Δ}
     → λC⁻ Γ ⊢      B , (B , Δ)
     → λC⁻ Γ ⊢           B , Δ
cᴿ₁′ f = ⇒ₑᵏ (# 0) (raa f)

-- Proof: contraction of identical contexts follows easily by
-- induction from the derived rules for contaction above.
cᴸ  : ∀ (Γ₁ Γ₂ : List Type) {A Δ}
    → λC⁻ Γ₁ ++ Γ₁ ++ Γ₂ ⊢[ A ] Δ
    → λC⁻ Γ₁       ++ Γ₂ ⊢[ A ] Δ
cᴸ       ·   Γ₂ f = f
cᴸ  (A , Γ₁) Γ₂ f = eᴸ · (A , ·) Γ₁ Γ₂ (cᴸ Γ₁ (A , Γ₂) lem₁)
  where
  lem₀ : λC⁻ A , (Γ₁ ++ Γ₁) ++ Γ₂ ⊢[ _ ] _
  lem₀ rewrite      assoc Γ₁ Γ₁      Γ₂   = cᴸ₁ (eᴸ · (A , ·) (A , Γ₁) (Γ₁ ++ Γ₂) f)
  lem₁ : λC⁻ Γ₁ ++ (Γ₁ ++ A , Γ₂) ⊢[ _ ] _
  lem₁ rewrite sym (assoc Γ₁ Γ₁ (A , Γ₂)) = eᴸ · (Γ₁ ++ Γ₁) (A , ·) Γ₂ lem₀

cᴸ′  : ∀ (Γ₁ Γ₂ : List Type) {Δ}
     → λC⁻ Γ₁ ++ Γ₁ ++ Γ₂ ⊢      Δ
     → λC⁻ Γ₁       ++ Γ₂ ⊢      Δ
cᴸ′ Γ₁ Γ₂ (⇒ₑᵏ α f) = ⇒ₑᵏ α (cᴸ Γ₁ Γ₂ f)

  
