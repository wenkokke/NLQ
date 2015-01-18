open import Level                                 using (Level; _⊔_)
open import Algebra                               using (module Monoid)
open import Function                              using (const; _∘_)
open import Data.Empty                            using (⊥)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List as List                     using (List; _++_; length) renaming ([] to ·; _∷_ to _,_; _∷ʳ_ to _,ʳ_)
open import Data.Nat                              using (ℕ; suc; zero; _+_)
open import Data.Nat.Properties.Simple            using (+-right-identity)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; uncurry′)
open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

module AHS.Implicit {ℓ₁} (Univ : Set ℓ₁) where

open import AHS.Type Univ as Type hiding (module ToAgda)
open Monoid (List.monoid Type) using (identity; assoc)

infix  1 AHS_
infixl 5 _‼_

_‼_ : ∀ {a} {A : Set a} → (xs : List A) (i : Fin (length xs)) → A
(    ·) ‼ ()
(x , Γ) ‼ zero  = x
(_ , Γ) ‼ suc i = Γ ‼ i


data AHS_ : Judgement → Set ℓ₁ where

  ax   : ∀ {Γ Δ}
       → (x : Fin (length Γ))
       → AHS     Γ ⊢[ Γ ‼ x ]     Δ

  ⇾ᵢ   : ∀ {Γ A B Δ}
       → AHS A , Γ ⊢[     B ]     Δ
       → AHS     Γ ⊢[ A ⇾ B ]     Δ

  ⇾ₑ   : ∀ {Γ A B Δ}
       → AHS     Γ ⊢[ A ⇾ B ]     Δ
       → AHS     Γ ⊢[ A     ]     Δ
       → AHS     Γ ⊢[     B ]     Δ

  raa  : ∀ {Γ A Δ}
       → AHS     Γ ⊢          A , Δ
       → AHS     Γ ⊢[ A     ]     Δ

  ⇾ₑᵏ  : ∀ {Γ Δ}
       → (α : Fin (length Δ))
       → AHS     Γ ⊢[ Δ ‼ α ]     Δ
       → AHS     Γ ⊢              Δ

  -ᵢ   : ∀ {Γ A B Δ}
       → AHS     Γ ⊢[ A     ]     Δ
       → AHS B , Γ ⊢              Δ
       → AHS     Γ ⊢[ A - B ]     Δ

  -ₑ   : ∀ {Γ A B C Δ}
       → AHS     Γ ⊢[ A - B ]     Δ
       → AHS A , Γ ⊢[ C     ] B , Δ
       → AHS     Γ ⊢[ C     ]     Δ


--------------------------------------------------------------------------------
-- Lemma: eˣ shows that we can, given a de Bruijn index `x` into a context
--        `(Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄)`, compute a new index `y` which will point
--        to the same value in the permuted context `(Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄)`.
--------------------------------------------------------------------------------

private
  m2fˣ  : ∀ {A} (Γ₁ Γ₂ : List Type) (x : _) → Σ[ y ∈ _ ]
          Γ₁ ++ A , Γ₂ ‼ x ≡ A , Γ₁ ++ Γ₂ ‼ y
  m2fˣ       ·   Γ₂  x      =   x , refl
  m2fˣ  (_ , Γ₁) Γ₂  zero   = # 1 , refl
  m2fˣ  (_ , Γ₁) Γ₂ (suc x) with (m2fˣ Γ₁ Γ₂ x)
  m2fˣ  (_ , Γ₁) Γ₂ (suc x) | zero  , p = zero        , p
  m2fˣ  (_ , Γ₁) Γ₂ (suc x) | suc y , p = suc (suc y) , p

  m2mˣ  : ∀ {A} (Γ₁ Γ₂ Γ₃ : List Type) (x : _) → Σ[ y ∈ _ ]
          Γ₁ ++ Γ₂ ++ A , Γ₃ ‼ x  ≡ Γ₁ ++ A , Γ₂ ++ Γ₃ ‼ y
  m2mˣ      ·   Γ₂ Γ₃  x      = m2fˣ Γ₂ Γ₃ x
  m2mˣ (_ , Γ₁) Γ₂ Γ₃  zero   = zero , refl
  m2mˣ (_ , Γ₁) Γ₂ Γ₃ (suc x) with (m2mˣ Γ₁ Γ₂ Γ₃ x)
  m2mˣ (_ , Γ₁) Γ₂ Γ₃ (suc x) | y , p = suc y , p
  
  eˣ   : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type)
       →  ( x : _ ) → Σ[ y ∈ _ ]
          (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ‼ x ≡ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ‼ y
  eˣ   Γ₁ Γ₂ Γ₃ Γ₄ rewrite assoc Γ₁ Γ₃ (Γ₂ ++ Γ₄) | assoc Γ₁ Γ₂ (Γ₃ ++ Γ₄) = eˣ′ Γ₁ Γ₂ Γ₃ Γ₄
    where
      eˣ′   : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) (x : _) → Σ[ y ∈ _ ]
             Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄ ‼ x ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄ ‼ y
      eˣ′ Γ₁      ·   Γ₃ Γ₄ x rewrite proj₂ identity Γ₁ | assoc Γ₁ Γ₃ Γ₄ = x , refl
      eˣ′ Γ₁ (A , Γ₂) Γ₃ Γ₄ x = l₃
        where
          l₁ : Σ[ y ∈ _ ] Γ₁ ++ Γ₃ ++ A , Γ₂ ++ Γ₄ ‼ x ≡ (Γ₁ ,ʳ A) ++ Γ₃ ++ Γ₂ ++ Γ₄ ‼ y
          l₁ rewrite sym (assoc (Γ₁ ,ʳ A) Γ₃ (Γ₂ ++ Γ₄)) | assoc Γ₁ (A , ·) Γ₃ | assoc Γ₁ (A , Γ₃) (Γ₂ ++ Γ₄) = m2mˣ {A} Γ₁ Γ₃ (Γ₂ ++ Γ₄) x
          l₂ : Σ[ y ∈ _ ] Γ₁ ++ Γ₃ ++ A , Γ₂ ++ Γ₄ ‼ x ≡ (Γ₁ ,ʳ A) ++ Γ₂ ++ Γ₃ ++ Γ₄ ‼ y
          l₂ with l₁
          l₂ | y , p with (eˣ′ (Γ₁ ,ʳ A) Γ₂ Γ₃ Γ₄ y)
          l₂ | y , p | z , q = z , trans p q
          l₃ : Σ[ y ∈ _ ] Γ₁ ++ Γ₃ ++ A , Γ₂ ++ Γ₄ ‼ x ≡ Γ₁ ++ A , Γ₂ ++ Γ₃ ++ Γ₄ ‼ y
          l₃ rewrite sym (assoc Γ₁ (A , Γ₂) (Γ₃ ++ Γ₄)) | sym (assoc Γ₁ (A , ·) Γ₂) | assoc (Γ₁ ,ʳ A) Γ₂ (Γ₃ ++ Γ₄) = l₂
  
  

mutual
  eᴸ   : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) {A Δ}
       → AHS (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢[ A ] Δ
       → AHS (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢[ A ] Δ
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (ax  x)   with (eˣ Γ₁ Γ₂ Γ₃ Γ₄ x)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (ax  x)   | y , p rewrite p = ax y
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⇾ᵢ  f)   = ⇾ᵢ  (eᴸ  (_ , Γ₁) Γ₂ Γ₃ Γ₄ f)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⇾ₑ  f g) = ⇾ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (raa f)   = raa (eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ f)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (-ᵢ  f g) = -ᵢ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ′ (_ , Γ₁) Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (-ₑ  f g) = -ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ  (_ , Γ₁) Γ₂ Γ₃ Γ₄ g)     

  eᴸ′  : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) {Δ}
       → AHS (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢      Δ
       → AHS (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢      Δ
  eᴸ′  Γ₁ Γ₂ Γ₃ Γ₄ (⇾ₑᵏ α f) = ⇾ₑᵏ α (eᴸ Γ₁ Γ₂ Γ₃ Γ₄ f)     


mutual
  eᴿ   : ∀ {Γ A} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → AHS Γ ⊢[ A ] (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → AHS Γ ⊢[ A ] (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (ax  x)   = ax x
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇾ᵢ  f)   = ⇾ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇾ₑ  f g) = ⇾ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (raa f)   = raa (eᴿ′ (_ , Δ₁) Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ᵢ  f g) = -ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ′      Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ₑ  f g) = -ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ  (_ , Δ₁) Δ₂ Δ₃ Δ₄ g)

  eᴿ′  : ∀ {Γ} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → AHS Γ ⊢      (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → AHS Γ ⊢      (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇾ₑᵏ α f) with (eˣ Δ₁ Δ₂ Δ₃ Δ₄ α)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇾ₑᵏ α f) | β , p rewrite p = ⇾ₑᵏ β (eᴿ Δ₁ Δ₂ Δ₃ Δ₄ f)
