open import Level            using (Level; suc; zero; _⊔_)
open import Function         using (_∘_)
open import Data.Empty       using (⊥)
open import Data.List        using (List; _++_; map) renaming ([] to ·; _∷_ to _,_)
open import Data.Product     using (_×_; _,_; uncurry′)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality as P

module AHS.Explicit {ℓ₁} (Univ : Set ℓ₁) where

open import AHS.Type Univ as Type hiding (module ToAgda)

infix  1 AHS_

data AHS_ : Judgement → Set ℓ₁ where

  ax   : ∀ {A Δ}
       → AHS A , ·        ⊢[ A     ]     Δ
 
  ⇾ᵢ   : ∀ {Γ A B Δ}
       → AHS A , Γ        ⊢[     B ]     Δ
       → AHS     Γ        ⊢[ A ⇾ B ]     Δ

  ⇾ₑ   : ∀ {Γ₁ Γ₂ A B Δ}
       → AHS Γ₁           ⊢[ A ⇾ B ]     Δ
       → AHS       Γ₂     ⊢[ A     ]     Δ
       → AHS Γ₁ ++ Γ₂     ⊢[     B ]     Δ

  raa  : ∀ {Γ A Δ}
       → AHS Γ            ⊢          A , Δ
       → AHS Γ            ⊢[ A     ]     Δ

  ⇾ₑᵏ  : ∀ {Γ A Δ}
       → AHS Γ            ⊢[ A     ] A , Δ
       → AHS Γ            ⊢          A , Δ

  -ᵢ   : ∀ {Γ₁ Γ₂ A B Δ}
       → AHS     Γ₁       ⊢[ A     ]     Δ
       → AHS B ,       Γ₂ ⊢              Δ
       → AHS     Γ₁ ++ Γ₂ ⊢[ A - B ]     Δ

  -ₑ   : ∀ {Γ₁ Γ₂ A B C Δ}
       → AHS     Γ₁       ⊢[ A - B ]     Δ
       → AHS A ,       Γ₂ ⊢[ C     ] B , Δ
       → AHS     Γ₁ ++ Γ₂ ⊢[ C     ]     Δ

  eᴸ   : ∀ Γ₁ Γ₂ Γ₃ Γ₄ {A Δ}
       → AHS (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢[ A ] Δ
       → AHS (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢[ A ] Δ

  eᴸ′  : ∀ Γ₁ Γ₂ Γ₃ Γ₄ {Δ}
       → AHS (Γ₁ ++ Γ₃) ++ (Γ₂ ++ Γ₄) ⊢      Δ
       → AHS (Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄) ⊢      Δ

  cᴸ₁  : ∀ {Γ A B Δ}
       → AHS A , (A , Γ) ⊢[ B ] Δ
       → AHS      A , Γ ⊢[ B ] Δ

  cᴸ₁′ : ∀ {Γ A Δ}
       → AHS A , (A , Γ) ⊢      Δ
       → AHS      A , Γ ⊢      Δ

  wᴸ₁  : ∀ {Γ A B Δ}
       → AHS     Γ ⊢[ B ] Δ
       → AHS A , Γ ⊢[ B ] Δ

  wᴸ₁′ : ∀ {Γ A Δ}
       → AHS     Γ ⊢      Δ
       → AHS A , Γ ⊢      Δ

  eᴿ   : ∀ {Γ A} Δ₁ Δ₂ Δ₃ Δ₄
       → AHS Γ ⊢[ A ] (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → AHS Γ ⊢[ A ] (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)

  eᴿ′  : ∀ {Γ  } Δ₁ Δ₂ Δ₃ Δ₄
       → AHS Γ ⊢      (Δ₁ ++ Δ₃) ++ (Δ₂ ++ Δ₄)
       → AHS Γ ⊢      (Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄)
   


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


-- Proof: full weakening for left-hand side context
--        follows easily from the simplified weakening.
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


-- Proof: contraction for the right-hand side
--        context follows from the axioms.
cᴿ₁  : ∀ {Γ A Δ}
     → AHS Γ ⊢[ A ] A , Δ
     → AHS Γ ⊢[ A ]     Δ
cᴿ₁  f = raa (⇾ₑᵏ f)

cᴿ₁′ : ∀ {Γ A Δ}
     → AHS Γ ⊢ A , (A , Δ)
     → AHS Γ ⊢      A , Δ
cᴿ₁′ f = ⇾ₑᵏ (raa f)


-- Lemma: simplified weakening for the right-hand
--        side context follows from the axioms.
mutual
  wᴿ₁  : ∀ {Γ A B Δ}
       → AHS Γ ⊢[ A ]     Δ
       → AHS Γ ⊢[ A ] B , Δ
  wᴿ₁  (ax                 ) = ax
  wᴿ₁  (⇾ᵢ              f  ) = ⇾ᵢ (wᴿ₁ f)
  wᴿ₁  (⇾ₑ              f g) = ⇾ₑ (wᴿ₁ f) (wᴿ₁ g)
  wᴿ₁  (raa             f  ) = raa (eᴿ₁′ (wᴿ₁′ f))
  wᴿ₁  (-ᵢ              f g) = -ᵢ (wᴿ₁ f) (wᴿ₁′ g)
  wᴿ₁  (-ₑ              f g) = -ₑ (wᴿ₁ f) (eᴿ₁ (wᴿ₁ g))
  wᴿ₁  (eᴸ  Γ₁ Γ₂ Γ₃ Γ₄ f  ) = eᴸ      Γ₁  Γ₂ Γ₃ Γ₄ (wᴿ₁ f)
  wᴿ₁  (cᴸ₁             f  ) = cᴸ₁ (wᴿ₁ f)
  wᴿ₁  (wᴸ₁             f  ) = wᴸ₁ (wᴿ₁ f)
  wᴿ₁  (eᴿ  Δ₁ Δ₂ Δ₃ Δ₄ f  ) = eᴿ (_ , Δ₁) Δ₂ Δ₃ Δ₄ (wᴿ₁ f)
   
  wᴿ₁′ : ∀ {Γ   B Δ}
       → AHS Γ ⊢          Δ
       → AHS Γ ⊢      B , Δ
  wᴿ₁′ (⇾ₑᵏ             f  ) = eᴿ₁′ (⇾ₑᵏ (eᴿ₁ (wᴿ₁ f)))
  wᴿ₁′ (eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄ f  ) = eᴸ′      Γ₁  Γ₂ Γ₃ Γ₄ (wᴿ₁′ f)
  wᴿ₁′ (cᴸ₁′            f  ) = cᴸ₁′ (wᴿ₁′ f)
  wᴿ₁′ (wᴸ₁′            f  ) = wᴸ₁′ (wᴿ₁′ f)
  wᴿ₁′ (eᴿ′ Δ₁ Δ₂ Δ₃ Δ₄ f  ) = eᴿ′ (_ , Δ₁) Δ₂ Δ₃ Δ₄ (wᴿ₁′ f)


-- Proof: full weakening for right-hand side context
--        follows easily from the simplified weakening.
wᴿ  : ∀ {Γ A} Δ₁ {Δ₂} → AHS Γ ⊢[ A ] Δ₂ → AHS Γ ⊢[ A ] Δ₁ ++ Δ₂
wᴿ       ·   f = f
wᴿ  (A , Δ₁) f = wᴿ₁  (wᴿ  Δ₁ f)

wᴿ′ : ∀ {Γ} Δ₁ {Δ₂} → AHS Γ ⊢      Δ₂ → AHS Γ ⊢      Δ₁ ++ Δ₂
wᴿ′      ·   f = f
wᴿ′ (A , Δ₁) f = wᴿ₁′ (wᴿ′ Δ₁ f) 


-- Proof: the system AHS can be translated to Agda by means of a
-- Fisher-style call-by-value CPS translation.
module ToAgda {ℓ₂} (⟦_⟧ᵁ : Univ → Set ℓ₂) where

  open Type.ToAgda ⟦_⟧ᵁ

  ⟦_⟧ : ∀ {J} → AHS J → λΠ J
  ⟦ ax                   ⟧ (x , _) (k , _) = k x
  ⟦ ⇾ᵢ               f   ⟧      e  (k , r) = k (λ k x → ⟦ f ⟧ (x , e) (k , r))
  ⟦ ⇾ₑ               f g ⟧      e  (k , r) = split e into λ e₁ e₂
                                           → ⟦ f ⟧ e₁ ((λ x → ⟦ g ⟧ e₂ (x k , r)) , r)
  ⟦ raa              f   ⟧      e  (k , r) = ⟦ f ⟧ e (     k , r )
  ⟦ ⇾ₑᵏ              f   ⟧      e  (k , r) = ⟦ f ⟧ e (k , (k , r))
  ⟦ -ᵢ               f g ⟧      e  (k , r) = split e into λ e₁ e₂
                                           → ⟦ f ⟧ e₁ ((λ x → k ((λ y → ⟦ g ⟧ (y , e₂) r) , x)) , r) 
  ⟦ -ₑ               f g ⟧      e  (k , r) = split e into λ e₁ e₂
                                           → ⟦ f ⟧ e₁ ((λ {(x , y) → ⟦ g ⟧ (y , e₂) (k , (x , r))}) , r)
  ⟦ eᴸ  Γ₁ Γ₂ Γ₃ Γ₄  f   ⟧      e  (k , r) = ⟦ f ⟧ (exchange Γ₁ Γ₃ Γ₂ Γ₄ e) (k , r)
  ⟦ eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄  f   ⟧      e       r  = ⟦ f ⟧ (exchange Γ₁ Γ₃ Γ₂ Γ₄ e)      r
  ⟦ cᴸ₁              f   ⟧ (x , e) (k , r) = ⟦ f ⟧ (x , (x , e)) (k , r)
  ⟦ cᴸ₁′             f   ⟧ (x , e)      r  = ⟦ f ⟧ (x , (x , e))      r
  ⟦ wᴸ₁              f   ⟧ (x , e) (k , r) = ⟦ f ⟧          e  (k , r)
  ⟦ wᴸ₁′             f   ⟧ (x , e)      r  = ⟦ f ⟧          e       r
  ⟦ eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ f   ⟧      e  (k , r) = ⟦ f ⟧ e (k , exchange Δ₁ Δ₃ Δ₂ Δ₄ r)
  ⟦ eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ f   ⟧      e       r  = ⟦ f ⟧ e (    exchange Δ₁ Δ₃ Δ₂ Δ₄ r)


