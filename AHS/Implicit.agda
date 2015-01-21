open import Algebra                               using (module Monoid)
open import Function                              using (_∘_)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List as List                     using (List; _++_; length) renaming ([] to ·; _∷_ to _,_; _∷ʳ_ to _,ʳ_)
open import Data.Product                          using (Σ; Σ-syntax; _×_; _,_; proj₂; uncurry′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)


module AHS.Implicit {ℓ₁} (Univ : Set ℓ₁) where


open import AHS.Type Univ as Type hiding (module ToAgda)
open Monoid (List.monoid Type) using (identity; assoc)


infix  1 AHS_


data AHS_ : Judgement → Set ℓ₁ where

  ax   : ∀ {Γ Δ}
       → (x : Fin (length Γ))
       → AHS     Γ ⊢[ Γ ‼ x ]     Δ

  ⇒ᵢ   : ∀ {Γ A B Δ}
       → AHS A , Γ ⊢[     B ]     Δ
       → AHS     Γ ⊢[ A ⇒ B ]     Δ

  ⇒ₑ   : ∀ {Γ A B Δ}
       → AHS     Γ ⊢[ A ⇒ B ]     Δ
       → AHS     Γ ⊢[ A     ]     Δ
       → AHS     Γ ⊢[     B ]     Δ

  raa  : ∀ {Γ A Δ}
       → AHS     Γ ⊢          A , Δ
       → AHS     Γ ⊢[ A     ]     Δ

  ⇒ₑᵏ  : ∀ {Γ Δ}
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

  ⊗ᵢ   : ∀ {Γ A B Δ}
       → AHS Γ ⊢[ A     ] Δ
       → AHS Γ ⊢[     B ] Δ
       → AHS Γ ⊢[ A ⊗ B ] Δ

  ⊗ₑ   : ∀ {Γ A B C Δ}
       → AHS          Γ  ⊢[ A ⊗ B ] Δ
       → AHS A , (B , Γ) ⊢[ C     ] Δ
       → AHS          Γ  ⊢[ C     ] Δ


-- Lemma: eˣ shows that we can, given a de Bruijn index `x` into a
--        context `(Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄)`, compute a new index `y`
--        which will point to the same value in the permuted context
--        `(Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄)`. 
private
  eˣ : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) (x : _) → Σ[ y ∈ _ ]
         (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ‼ x ≡ (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ‼ y
  eˣ Γ₁ Γ₂ Γ₃ Γ₄ rewrite assoc Γ₁ Γ₃ (Γ₂ ++ Γ₄) | assoc Γ₁ Γ₂ (Γ₃ ++ Γ₄) = eˣ′ Γ₁ Γ₂ Γ₃ Γ₄
    where
      m2fˣ : ∀ {A} (Γ₁ Γ₂ : List Type) (x : _) → Σ[ y ∈ _ ]
             Γ₁ ++ A , Γ₂ ‼ x ≡ A , Γ₁ ++ Γ₂ ‼ y
      m2fˣ      ·   Γ₂  x      =   x , refl
      m2fˣ (_ , Γ₁) Γ₂  zero   = # 1 , refl
      m2fˣ (_ , Γ₁) Γ₂ (suc x) with (m2fˣ Γ₁ Γ₂ x)
      m2fˣ (_ , Γ₁) Γ₂ (suc x) | zero  , p = zero        , p
      m2fˣ (_ , Γ₁) Γ₂ (suc x) | suc y , p = suc (suc y) , p

      m2mˣ : ∀ {A} (Γ₁ Γ₂ Γ₃ : List Type) (x : _) → Σ[ y ∈ _ ]
             Γ₁ ++ Γ₂ ++ A , Γ₃ ‼ x  ≡ Γ₁ ++ A , Γ₂ ++ Γ₃ ‼ y
      m2mˣ      ·   Γ₂ Γ₃  x      = m2fˣ Γ₂ Γ₃ x
      m2mˣ (_ , Γ₁) Γ₂ Γ₃  zero   = zero , refl
      m2mˣ (_ , Γ₁) Γ₂ Γ₃ (suc x) with (m2mˣ Γ₁ Γ₂ Γ₃ x)
      m2mˣ (_ , Γ₁) Γ₂ Γ₃ (suc x) | y , p = suc y , p

      eˣ′ : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) (x : _) → Σ[ y ∈ _ ]
            Γ₁ ++ Γ₃ ++ Γ₂ ++ Γ₄ ‼ x ≡ Γ₁ ++ Γ₂ ++ Γ₃ ++ Γ₄ ‼ y
      eˣ′ Γ₁      ·   Γ₃ Γ₄ x rewrite proj₂ identity Γ₁ | assoc Γ₁ Γ₃ Γ₄ = x , refl
      eˣ′ Γ₁ (A , Γ₂) Γ₃ Γ₄ x = l₃
        where
          l₁ : Σ[ y ∈ _ ] Γ₁ ++ Γ₃ ++ A , Γ₂ ++ Γ₄ ‼ x ≡ (Γ₁ ,ʳ A) ++ Γ₃ ++ Γ₂ ++ Γ₄ ‼ y
          l₁ rewrite sym (assoc (Γ₁ ,ʳ A) Γ₃ (Γ₂ ++ Γ₄))
                   | assoc Γ₁ (A , ·) Γ₃
                   | assoc Γ₁ (A , Γ₃) (Γ₂ ++ Γ₄)
                   = m2mˣ {A} Γ₁ Γ₃ (Γ₂ ++ Γ₄) x
          l₂ : Σ[ y ∈ _ ] Γ₁ ++ Γ₃ ++ A , Γ₂ ++ Γ₄ ‼ x ≡ (Γ₁ ,ʳ A) ++ Γ₂ ++ Γ₃ ++ Γ₄ ‼ y
          l₂ with l₁
          l₂ | y , p with (eˣ′ (Γ₁ ,ʳ A) Γ₂ Γ₃ Γ₄ y)
          l₂ | y , p | z , q = z , trans p q
          l₃ : Σ[ y ∈ _ ] Γ₁ ++ Γ₃ ++ A , Γ₂ ++ Γ₄ ‼ x ≡ Γ₁ ++ A , Γ₂ ++ Γ₃ ++ Γ₄ ‼ y
          l₃ rewrite sym (assoc Γ₁ (A , Γ₂) (Γ₃ ++ Γ₄))
                   | sym (assoc Γ₁ (A , ·) Γ₂)
                   | assoc (Γ₁ ,ʳ A) Γ₂ (Γ₃ ++ Γ₄) = l₂


-- Proof: eᴸ and eᴿ show that the structural rules of left and right
-- exchange are implicit in the axiomatisation that we've chosen.
mutual
  eᴸ   : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) {A Δ}
       → AHS (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢[ A ] Δ
       → AHS (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢[ A ] Δ
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (ax  x)   with (eˣ Γ₁ Γ₂ Γ₃ Γ₄ x)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (ax  x)   | y , p rewrite p = ax y
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⇒ᵢ  f)   = ⇒ᵢ  (eᴸ  (_ , Γ₁) Γ₂ Γ₃ Γ₄ f)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⇒ₑ  f g) = ⇒ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ            Γ₁   Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (raa f)   = raa (eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ f)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (-ᵢ  f g) = -ᵢ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ′      (_ , Γ₁)  Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (-ₑ  f g) = -ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ       (_ , Γ₁)  Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⊗ᵢ  f g) = ⊗ᵢ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ            Γ₁   Γ₂ Γ₃ Γ₄ g)
  eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (⊗ₑ  f g) = ⊗ₑ  (eᴸ       Γ₁  Γ₂ Γ₃ Γ₄ f) (eᴸ  (_ , (_ , Γ₁)) Γ₂ Γ₃ Γ₄ g)

  eᴸ′  : ∀ (Γ₁ Γ₂ Γ₃ Γ₄ : List Type) {Δ}
       → AHS (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢      Δ
       → AHS (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢      Δ
  eᴸ′  Γ₁ Γ₂ Γ₃ Γ₄ (⇒ₑᵏ α f) = ⇒ₑᵏ α (eᴸ Γ₁ Γ₂ Γ₃ Γ₄ f)
  

-- Lemma: weaker version of exchange which swaps
--        the first two elements in the context.
eᴸ₁  : ∀ {Γ A B C Δ}
     → AHS B , (A , Γ) ⊢[ C ] Δ
     → AHS A , (B , Γ) ⊢[ C ] Δ
eᴸ₁  = eᴸ · (_ , ·) (_ , ·) _

eᴸ₁′ : ∀ {Γ A B Δ}
     → AHS B , (A , Γ) ⊢      Δ
     → AHS A , (B , Γ) ⊢      Δ
eᴸ₁′ = eᴸ′ · (_ , ·) (_ , ·) _

eᴸ₂  : ∀ {Γ A B C D Δ}
     → AHS C , (A , (B , Γ)) ⊢[ D ] Δ
     → AHS A , (B , (C , Γ)) ⊢[ D ] Δ
eᴸ₂  = eᴸ · (_ , (_ , ·)) (_ , ·) _



-- Lemma: simplified exchange which swaps two
--        contexts.
sᴸ  : ∀ (Γ₁ Γ₂ : List Type) {A Δ} → AHS Γ₂ ++ Γ₁ ⊢[ A ] Δ → AHS Γ₁ ++ Γ₂ ⊢[ A ] Δ
sᴸ  ·  Γ₂ {A} {Δ} = subst  (λ Γ → AHS Γ ⊢[ A ] Δ) (     proj₂ identity Γ₂ )
sᴸ  Γ₁ ·  {A} {Δ} = subst  (λ Γ → AHS Γ ⊢[ A ] Δ) (sym (proj₂ identity Γ₁))
sᴸ  Γ₁ Γ₂ {A} {Δ} = subst₂ (λ Γ₁′ Γ₂′ → AHS Γ₂ ++ Γ₁′ ⊢[ A ] Δ → AHS Γ₁ ++ Γ₂′ ⊢[ A ] Δ) (proj₂ identity Γ₁) (proj₂ identity Γ₂) (eᴸ  · Γ₁ Γ₂ ·)

sᴸ′ : ∀ (Γ₁ Γ₂ : List Type) {Δ} → AHS Γ₂ ++ Γ₁ ⊢ Δ → AHS Γ₁ ++ Γ₂ ⊢ Δ
sᴸ′ ·  Γ₂ {Δ} = subst  (λ Γ → AHS Γ ⊢ Δ) (     proj₂ identity Γ₂ )
sᴸ′ Γ₁ ·  {Δ} = subst  (λ Γ → AHS Γ ⊢ Δ) (sym (proj₂ identity Γ₁))
sᴸ′ Γ₁ Γ₂ {Δ} = subst₂ (λ Γ₁′ Γ₂′ → AHS Γ₂ ++ Γ₁′ ⊢ Δ → AHS Γ₁ ++ Γ₂′ ⊢ Δ) (proj₂ identity Γ₁) (proj₂ identity Γ₂) (eᴸ′ · Γ₁ Γ₂ ·)


mutual
  eᴿ   : ∀ {Γ A} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → AHS Γ ⊢[ A ] (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → AHS Γ ⊢[ A ] (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (ax  x)   = ax x
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇒ᵢ  f)   = ⇒ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑ  f g) = ⇒ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (raa f)   = raa (eᴿ′ (_ , Δ₁) Δ₂ Δ₃ Δ₄ f)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ᵢ  f g) = -ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ′      Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (-ₑ  f g) = -ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ  (_ , Δ₁) Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⊗ᵢ  f g) = ⊗ᵢ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)
  eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (⊗ₑ  f g) = ⊗ₑ  (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ f) (eᴿ       Δ₁  Δ₂ Δ₃ Δ₄ g)

  eᴿ′  : ∀ {Γ} (Δ₁ Δ₂ Δ₃ Δ₄ : List Type)
       → AHS Γ ⊢      (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → AHS Γ ⊢      (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑᵏ α f) with (eˣ Δ₁ Δ₂ Δ₃ Δ₄ α)
  eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (⇒ₑᵏ α f) | β , p rewrite p = ⇒ₑᵏ β (eᴿ Δ₁ Δ₂ Δ₃ Δ₄ f)


-- Lemma: simplified exchange which swaps the
--        first two elements in the context.
eᴿ₁  : ∀ {Γ A B C Δ}
     → AHS Γ ⊢[ A ] C , (B , Δ)
     → AHS Γ ⊢[ A ] B , (C , Δ)
eᴿ₁  = eᴿ · (_ , ·) (_ , ·) _

eᴿ₁′ : ∀ {Γ B C Δ}
     → AHS Γ ⊢      C , (B , Δ)
     → AHS Γ ⊢      B , (C , Δ)
eᴿ₁′ = eᴿ′ · (_ , ·) (_ , ·) _


-- Lemma: simplified exchange which swaps two contexts.
sᴿ  : ∀ {Γ A} (Δ₁ Δ₂ : List Type) → AHS Γ ⊢[ A ] Δ₂ ++ Δ₁ → AHS Γ ⊢[ A ] Δ₁ ++ Δ₂
sᴿ  ·  Δ₂ = subst  (λ Δ → AHS _ ⊢[ _ ] Δ) (     proj₂ identity Δ₂ )
sᴿ  Δ₁ ·  = subst  (λ Δ → AHS _ ⊢[ _ ] Δ) (sym (proj₂ identity Δ₁))
sᴿ  Δ₁ Δ₂ = subst₂ (λ Δ₁′ Δ₂′ → AHS _ ⊢[ _ ] Δ₂ ++ Δ₁′ → AHS _ ⊢[ _ ] Δ₁ ++ Δ₂′) (proj₂ identity Δ₁) (proj₂ identity Δ₂) (eᴿ  · Δ₁ Δ₂ ·)

sᴿ′ : ∀ {Γ} (Δ₁ Δ₂ : List Type) → AHS Γ ⊢ Δ₂ ++ Δ₁ → AHS Γ ⊢ Δ₁ ++ Δ₂
sᴿ′ ·  Δ₂ = subst  (λ Δ → AHS _ ⊢ Δ) (     proj₂ identity Δ₂ )
sᴿ′ Δ₁ ·  = subst  (λ Δ → AHS _ ⊢ Δ) (sym (proj₂ identity Δ₁))
sᴿ′ Δ₁ Δ₂ = subst₂ (λ Δ₁′ Δ₂′ → AHS _ ⊢ Δ₂ ++ Δ₁′ → AHS _ ⊢ Δ₁ ++ Δ₂′) (proj₂ identity Δ₁) (proj₂ identity Δ₂) (eᴿ′ · Δ₁ Δ₂ ·)



-- Lemma: simplified weakening for the left-hand side context follows
-- from the axioms. 
mutual
  wᴸ₁  : ∀ {Γ A B Δ}
       → AHS     Γ ⊢[ B ] Δ
       → AHS A , Γ ⊢[ B ] Δ
  wᴸ₁ (ax  x)   = ax (suc x)
  wᴸ₁ (⇒ᵢ  f)   = ⇒ᵢ  (eᴸ₁ (wᴸ₁ f))
  wᴸ₁ (⇒ₑ  f g) = ⇒ₑ  (wᴸ₁  f) (wᴸ₁ g)
  wᴸ₁ (raa f)   = raa (wᴸ₁′ f)
  wᴸ₁ (-ᵢ  f g) = -ᵢ  (wᴸ₁  f) (eᴸ₁′ (wᴸ₁′ g))
  wᴸ₁ (-ₑ  f g) = -ₑ  (wᴸ₁  f) (eᴸ₁  (wᴸ₁  g))
  wᴸ₁ (⊗ᵢ  f g) = ⊗ᵢ  (wᴸ₁  f) (wᴸ₁ g)
  wᴸ₁ (⊗ₑ  f g) = ⊗ₑ  (wᴸ₁  f) (eᴸ₂ (wᴸ₁ g))
  
  wᴸ₁′ : ∀ {Γ A Δ}
       → AHS     Γ ⊢      Δ
       → AHS A , Γ ⊢      Δ
  wᴸ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ α (wᴸ₁ f)


-- Proof: full weakening for left-hand side context follows easily
-- from the simplified weakening. 
wᴸ  : ∀ Γ₁ {Γ₂ A Δ}
    → AHS       Γ₂ ⊢[ A ] Δ
    → AHS Γ₁ ++ Γ₂ ⊢[ A ] Δ
wᴸ       ·   f = f
wᴸ  (A , Γ₁) f = wᴸ₁  (wᴸ  Γ₁ f)

wᴸ′ : ∀ Γ₁ {Γ₂   Δ}
    → AHS       Γ₂ ⊢      Δ
    → AHS Γ₁ ++ Γ₂ ⊢      Δ
wᴸ′      ·   f = f
wᴸ′ (A , Γ₁) f = wᴸ₁′ (wᴸ′ Γ₁ f) 


-- Lemma: simplified weakening for the right-hand side context follows
-- from the axioms. 
mutual
  wᴿ₁  : ∀ {Γ A B Δ}
       → AHS Γ ⊢[ A ]     Δ
       → AHS Γ ⊢[ A ] B , Δ
  wᴿ₁  (ax  x)   = ax x
  wᴿ₁  (⇒ᵢ  f)   = ⇒ᵢ  (wᴿ₁  f)
  wᴿ₁  (⇒ₑ  f g) = ⇒ₑ  (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (raa f)   = raa (eᴿ₁′ (wᴿ₁′ f))
  wᴿ₁  (-ᵢ  f g) = -ᵢ  (wᴿ₁  f) (wᴿ₁′ g)
  wᴿ₁  (-ₑ  f g) = -ₑ  (wᴿ₁  f) (eᴿ₁ (wᴿ₁ g))
  wᴿ₁  (⊗ᵢ  f g) = ⊗ᵢ  (wᴿ₁  f) (wᴿ₁ g)
  wᴿ₁  (⊗ₑ  f g) = ⊗ₑ  (wᴿ₁  f) (wᴿ₁ g)

  wᴿ₁′ : ∀ {Γ A Δ}
       → AHS Γ ⊢          Δ
       → AHS Γ ⊢      A , Δ
  wᴿ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ (suc α) (wᴿ₁ f)


-- Proof: full weakening for right-hand side context
--        follows easily from the simplified weakening.
wᴿ  : ∀ {Γ A} Δ₁ {Δ₂} → AHS Γ ⊢[ A ] Δ₂ → AHS Γ ⊢[ A ] Δ₁ ++ Δ₂
wᴿ       ·   f = f
wᴿ  (A , Δ₁) f = wᴿ₁  (wᴿ  Δ₁ f)

wᴿ′ : ∀ {Γ} Δ₁ {Δ₂} → AHS Γ ⊢      Δ₂ → AHS Γ ⊢      Δ₁ ++ Δ₂
wᴿ′      ·   f = f
wᴿ′ (A , Δ₁) f = wᴿ₁′ (wᴿ′ Δ₁ f) 


-- Proof: contraction for the right-hand side
--        context follows from the axioms.
cᴸ₁  : ∀ {Γ A B Δ}
     → AHS A , (A , Γ) ⊢[ B ] Δ
     → AHS      A , Γ  ⊢[ B ] Δ
cᴸ₁  f = ⇒ₑ (⇒ᵢ f) (ax (# 0))

cᴸ₁′ : ∀ {Γ A Δ}
     → AHS A , (A , Γ) ⊢ Δ
     → AHS      A , Γ  ⊢ Δ
cᴸ₁′ (⇒ₑᵏ α f) = ⇒ₑᵏ α (cᴸ₁ f)



-- Proof: contraction for the right-hand side
--        context follows from the axioms.
cᴿ₁  : ∀ {Γ A Δ}
     → AHS Γ ⊢[ A ] A , Δ
     → AHS Γ ⊢[ A ]     Δ
cᴿ₁  f = raa (⇒ₑᵏ (# 0) f)

cᴿ₁′ : ∀ {Γ A Δ}
     → AHS Γ ⊢ A , (A , Δ)
     → AHS Γ ⊢      A , Δ
cᴿ₁′ f = ⇒ₑᵏ (# 0) (raa f)
