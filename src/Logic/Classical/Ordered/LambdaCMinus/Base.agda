open import Algebra                               using (module Monoid)
open import Function                              using (id; _∘_)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List                             using (List; _++_) renaming ([] to ∅; _∷_ to _,_; _∷ʳ_ to _,ʳ_)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map)
open import Data.Sum                              using (_⊎_; inj₁; inj₂)
open import Relation.Nullary.Decidable            using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)

module Logic.Classical.Ordered.LambdaCMinus.Base {ℓ} (Univ : Set ℓ) where


open import Logic.Index renaming (lookup to _‼_)
open import Logic.Type Univ renaming (_⇚_ to _-_)
open import Logic.Structure.Conjunction Univ
open import Logic.Classical.Judgement Conjunction Type (List Type)
open Monoid (Data.List.monoid Type) using (identity; assoc)


infix  1 λC⁻_

data λC⁻_ : Judgement → Set ℓ where

  ax   : ∀ {A Δ}
       → λC⁻ · A ·                   ⊢[ A     ]     Δ
 
  ⇒ᵢ   : ∀ {Γ A B Δ}
       → λC⁻ · A · ⊗ Γ               ⊢[     B ]     Δ
       → λC⁻         Γ               ⊢[ A ⇒ B ]     Δ

  ⇒ₑ   : ∀ {Γ₁ Γ₂ A B Δ}
       → λC⁻         Γ₁              ⊢[ A     ]     Δ
       → λC⁻              Γ₂         ⊢[ A ⇒ B ]     Δ
       → λC⁻         Γ₁ ⊗ Γ₂         ⊢[     B ]     Δ

  ⇐ᵢ   : ∀ {Γ A B Δ}
       → λC⁻         Γ       ⊗ · A · ⊢[ B     ]     Δ
       → λC⁻         Γ               ⊢[ B ⇐ A ]     Δ

  ⇐ₑ   : ∀ {Γ₁ Γ₂ A B Δ}
       → λC⁻         Γ₁              ⊢[ B ⇐ A ]     Δ
       → λC⁻              Γ₂         ⊢[ A     ]     Δ
       → λC⁻         Γ₁ ⊗ Γ₂         ⊢[     B ]     Δ

  raa  : ∀ {Γ A Δ}
       → λC⁻         Γ               ⊢          A , Δ
       → λC⁻         Γ               ⊢[ A ]         Δ

  ⇒ₑᵏ  : ∀ {Γ Δ} (α : Fin _)
       → λC⁻         Γ               ⊢[ Δ ‼ α ]     Δ
       → λC⁻         Γ               ⊢              Δ

  -ᵢ   : ∀ {Γ₁ Γ₂ A B Δ}
       → λC⁻         Γ₁              ⊢[ A     ]     Δ
       → λC⁻ · B · ⊗      Γ₂         ⊢              Δ
       → λC⁻         Γ₁ ⊗ Γ₂         ⊢[ A - B ]     Δ

  -ₑ   : ∀ {Γ₁ Γ₂ A B C Δ}
       → λC⁻         Γ₁              ⊢[ A - B ]     Δ
       → λC⁻ · A · ⊗      Γ₂         ⊢[ C     ] B , Δ
       → λC⁻         Γ₁ ⊗ Γ₂         ⊢[ C     ]     Δ

  ⊗ᵢ   : ∀ {Γ₁ Γ₂ A B Δ}
       → λC⁻         Γ₁              ⊢[ A     ]     Δ
       → λC⁻              Γ₂         ⊢[     B ]     Δ
       → λC⁻         Γ₁ ⊗ Γ₂         ⊢[ A ⊗ B ]     Δ

  ⊗ₑ   : ∀ {Γ₁} Γ₂ {A B C Δ}
       → λC⁻ Γ₁                      ⊢[ A ⊗ B ]     Δ
       → λC⁻ Γ₂ [ · A · ⊗ · B · ]    ⊢[ C     ]     Δ
       → λC⁻ Γ₂ [ Γ₁ ]               ⊢[ C     ]     Δ


-- Proof: eᴿ shows that the structural rule of right exchange is
-- implicit in the axiomatisation that we've chosen. 
mutual
  eᴿ   : ∀ {Γ A} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → λC⁻ Γ ⊢[ A ] (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → λC⁻ Γ ⊢[ A ] (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (ax                 ) = ax
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇒ᵢ              f  ) = ⇒ᵢ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑ              f g) = ⇒ₑ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇐ᵢ              f  ) = ⇐ᵢ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇐ₑ              f g) = ⇐ₑ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (raa             f  ) = raa   (eᴿ′ (_ , Δ₁) Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ᵢ              f g) = -ᵢ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ′      Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ₑ              f g) = -ₑ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ  (_ , Δ₁) Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⊗ᵢ              f g) = ⊗ᵢ    (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⊗ₑ  Γ           f g) = ⊗ₑ  Γ (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  
  eᴿ′  : ∀ {Γ} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → λC⁻ Γ ⊢      (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → λC⁻ Γ ⊢      (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑᵏ α f) with (exchange Δ₁ Δ₂ Δ₃ Δ₄ α)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑᵏ α f) | β , p rewrite p = ⇒ₑᵏ β (eᴿ Δ₁ Δ₂ Δ₃ Δ₄ f)


-- Lemma: weaker version of eᴿ which only swap the first two elements
-- are often useful. 
eᴿ₁  : ∀ {Γ A B C Δ}
     → λC⁻ Γ ⊢[ A ] C , (B , Δ)
     → λC⁻ Γ ⊢[ A ] B , (C , Δ)
eᴿ₁  = eᴿ ∅ (_ , ∅) (_ , ∅) _

eᴿ₁′ : ∀ {Γ B C Δ}
     → λC⁻ Γ ⊢      C , (B , Δ)
     → λC⁻ Γ ⊢      B , (C , Δ)
eᴿ₁′ = eᴿ′ ∅ (_ , ∅) (_ , ∅) _
  

-- Lemma: weaker version of eᴿ which only swap two contexts, without
-- allowing them to be embedded in further contexts are often useful
-- as well. 
sᴿ  : ∀ {Γ A} (Δ₁ Δ₂ : List Type) → λC⁻ Γ ⊢[ A ] Δ₂ ++ Δ₁ → λC⁻ Γ ⊢[ A ] Δ₁ ++ Δ₂
sᴿ  Δ₁ ∅  = subst  (λ Δ       → λC⁻ _ ⊢[ _ ]       Δ)                            (sym (proj₂ identity Δ₁))
sᴿ  ∅  Δ₂ = subst  (λ     Δ   → λC⁻ _ ⊢[ _ ] Δ      )                                                      (proj₂ identity Δ₂)
sᴿ  Δ₁ Δ₂ = subst₂ (λ Δ₁′ Δ₂′ → λC⁻ _ ⊢[ _ ] Δ₂ ++ Δ₁′ → λC⁻ _ ⊢[ _ ] Δ₁ ++ Δ₂′) (     proj₂ identity Δ₁ ) (proj₂ identity Δ₂) (eᴿ  ∅ Δ₁ Δ₂ ∅)

sᴿ′ : ∀ {Γ} (Δ₁ Δ₂ : List Type) → λC⁻ Γ ⊢ Δ₂ ++ Δ₁ → λC⁻ Γ ⊢ Δ₁ ++ Δ₂
sᴿ′ Δ₁ ∅  = subst  (λ Δ       → λC⁻ _ ⊢            Δ)                            (sym (proj₂ identity Δ₁))
sᴿ′ ∅  Δ₂ = subst  (λ     Δ   → λC⁻ _ ⊢      Δ      )                                                      (proj₂ identity Δ₂)
sᴿ′ Δ₁ Δ₂ = subst₂ (λ Δ₁′ Δ₂′ → λC⁻ _ ⊢      Δ₂ ++ Δ₁′ → λC⁻ _ ⊢      Δ₁ ++ Δ₂′) (     proj₂ identity Δ₁ ) (proj₂ identity Δ₂) (eᴿ′ ∅ Δ₁ Δ₂ ∅)


-- Lemma: weaker versions of weakning for which simply allows for the
-- addition of one unused premise can easily be induced from the
-- axioms.
mutual
  wᴿ₁  : ∀ {Γ A B Δ}
       → λC⁻ Γ ⊢[ A ]     Δ
       → λC⁻ Γ ⊢[ A ] B , Δ
  wᴿ₁  (ax                 ) = ax
  wᴿ₁  (⇒ᵢ              f  ) = ⇒ᵢ    (wᴿ₁  f)
  wᴿ₁  (⇒ₑ              f g) = ⇒ₑ    (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (⇐ᵢ              f  ) = ⇐ᵢ    (wᴿ₁  f)
  wᴿ₁  (⇐ₑ              f g) = ⇐ₑ    (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (raa             f  ) = raa   (eᴿ₁′ (wᴿ₁′ f))
  wᴿ₁  (-ᵢ              f g) = -ᵢ    (wᴿ₁  f) (wᴿ₁′ g)
  wᴿ₁  (-ₑ              f g) = -ₑ    (wᴿ₁  f) (eᴿ₁ (wᴿ₁ g))
  wᴿ₁  (⊗ᵢ              f g) = ⊗ᵢ    (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (⊗ₑ  Γ           f g) = ⊗ₑ  Γ (wᴿ₁  f) (wᴿ₁ g) 
  
  wᴿ₁′ : ∀ {Γ A Δ}
       → λC⁻ Γ ⊢          Δ
       → λC⁻ Γ ⊢      A , Δ
  wᴿ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ (suc α) (wᴿ₁ f)


-- Proof: weakening follows easily by induction from the simplified
-- versions of weakening proved above.
wᴿ  : ∀ {Γ A} Δ₁ {Δ₂}
    → λC⁻ Γ ⊢[ A ]       Δ₂
    → λC⁻ Γ ⊢[ A ] Δ₁ ++ Δ₂
wᴿ       ∅   f = f
wᴿ  (A , Δ₁) f = wᴿ₁  (wᴿ  Δ₁ f)

wᴿ′ : ∀ {Γ} Δ₁ {Δ₂}
    → λC⁻ Γ ⊢       Δ₂
    → λC⁻ Γ ⊢ Δ₁ ++ Δ₂
wᴿ′      ∅   f = f
wᴿ′ (A , Δ₁) f = wᴿ₁′ (wᴿ′ Δ₁ f)


-- There are two special versions for the right-hand sided lemmas,
-- |ėᴿ₁| and |ċᴿ₁|, which allow for exchange with and contraction into
-- focused expressions.
ėᴿ₁ : ∀ {Γ A B Δ}
     → λC⁻ Γ ⊢[ A ] B , Δ
     → λC⁻ Γ ⊢[ B ] A , Δ
ėᴿ₁ f = raa (⇒ₑᵏ (# 1) (eᴿ₁ (wᴿ₁ f)))

ċᴿ₁  : ∀ {Γ A Δ}
     → λC⁻ Γ ⊢[ A ] A , Δ
     → λC⁻ Γ ⊢[ A ]     Δ
ċᴿ₁  f = raa (⇒ₑᵏ (# 0) f)


-- Lemma: weaker versions of contraction, which contract two (co-)values of
-- the same type, can easily be derived from the axioms.
cᴿ₁  : ∀ {Γ A B Δ}
     → λC⁻ Γ ⊢[ A ] B , (B , Δ)
     → λC⁻ Γ ⊢[ A ]      B , Δ
cᴿ₁  f = ėᴿ₁ (ċᴿ₁ (eᴿ₁ (ėᴿ₁ f)))

cᴿ₁′ : ∀ {Γ B Δ}
     → λC⁻ Γ ⊢      B , (B , Δ)
     → λC⁻ Γ ⊢           B , Δ
cᴿ₁′ f = ⇒ₑᵏ (# 0) (raa f)

cᴿ  : ∀ {Γ A} (Δ₁ Δ₂ : List Type)
    → λC⁻ Γ ⊢[ A ] Δ₁ ++ Δ₁ ++ Δ₂
    → λC⁻ Γ ⊢[ A ]       Δ₁ ++ Δ₂
cᴿ      ∅   Δ₂ f = f
cᴿ (A , Δ₁) Δ₂ f = eᴿ ∅ (A , ∅) Δ₁ Δ₂ (cᴿ Δ₁ (A , Δ₂) lem₁)
  where
  lem₀ : λC⁻ _ ⊢[ _ ] A , (Δ₁ ++ Δ₁) ++ Δ₂
  lem₀ rewrite      assoc Δ₁ Δ₁      Δ₂   = cᴿ₁ (eᴿ ∅ (A , ∅) (A , Δ₁) (Δ₁ ++ Δ₂) f)
  lem₁ : λC⁻ _ ⊢[ _ ] Δ₁ ++ (Δ₁ ++ A , Δ₂)
  lem₁ rewrite sym (assoc Δ₁ Δ₁ (A , Δ₂)) = eᴿ ∅ (Δ₁ ++ Δ₁) (A , ∅) Δ₂ lem₀

cᴿ′ : ∀ {Γ} (Δ₁ Δ₂ : List Type)
    → λC⁻ Γ ⊢      Δ₁ ++ Δ₁ ++ Δ₂
    → λC⁻ Γ ⊢            Δ₁ ++ Δ₂
cᴿ′ Δ₁ Δ₂ (⇒ₑᵏ α f) with contract Δ₁ Δ₂ α
cᴿ′ Δ₁ Δ₂ (⇒ₑᵏ α f) | β , p rewrite p = ⇒ₑᵏ β (cᴿ Δ₁ Δ₂ f)

