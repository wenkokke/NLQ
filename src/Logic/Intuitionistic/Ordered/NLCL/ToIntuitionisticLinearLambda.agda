------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Data.List using (List; _++_) renaming (_∷_ to _,_; _∷ʳ_ to _,′_; [] to ∅)


module Logic.Intuitionistic.Ordered.NLCL.ToIntuitionisticLinearLambda {ℓ} (Univ : Set ℓ) where


open import Logic.Translation

open import Logic.Intuitionistic.Linear.Lambda.Type      Univ as ΛT
open import Logic.Intuitionistic.Linear.Lambda.Judgement Univ as ΛJ
open import Logic.Intuitionistic.Linear.Lambda.Base      Univ as ΛB
open import Logic.Intuitionistic.Linear.Lambda.Permute   Univ as ΛP

open import Logic.Intuitionistic.Ordered.NLCL.Type      Univ as NLT
open import Logic.Intuitionistic.Ordered.NLCL.Judgement Univ as NLJ
open import Logic.Intuitionistic.Ordered.NLCL.Base      Univ as NLB


module WithUnit (⊤ : Univ) (tt : Λ ∅ ⊢ el ⊤)  where

  ⊤ₑ : ∀ {A B} → Λ A ⊗ el ⊤ , ∅ ⊢ B → Λ A , ∅ ⊢ B
  ⊤ₑ f = ⇒ₑ (⇒ᵢ (eᴸ₁ (⇒ₑ (⇒ᵢ f) (⊗ᵢ ax ax)))) tt

  ⊤ᵢ : ∀ {A B} → Λ A , ∅ ⊢ B → Λ A ⊗ el ⊤ , ∅ ⊢ B
  ⊤ᵢ f = ⇒ₑ (⇒ᵢ f) (⊗ₑ {!!} {!!})

  ⟦_⟧ᵀ : NLT.Type → ΛT.Type
  ⟦ el  A ⟧ᵀ = el A
  ⟦     I ⟧ᵀ = el ⊤
  ⟦     L ⟧ᵀ = el ⊤
  ⟦     R ⟧ᵀ = el ⊤
  ⟦ A ⊗ B ⟧ᵀ = ⟦ A ⟧ᵀ ⊗ ⟦ B ⟧ᵀ
  ⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ
  ⟦ B ⇐ A ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ
  ⟦ A ∘ B ⟧ᵀ = ⟦ A ⟧ᵀ ⊗ ⟦ B ⟧ᵀ
  ⟦ A ⇨ B ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ
  ⟦ B ⇦ A ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ


  ⟦_⟧ᴶ : NLJ.Judgement → ΛJ.Judgement
  ⟦ A ⊢ B ⟧ᴶ = ⟦ A ⟧ᵀ , ∅ ⊢ ⟦ B ⟧ᵀ


  [_] : ∀ {J} → NL J → Λ ⟦ J ⟧ᴶ
  [ ax      ] = ax
  [ m⊗  f g ] = ⊗ₑᴸ₁ (⊗ᵢ [ f ] [ g ])
  [ m⇒  f g ] = ⇒ᵢ (⇒ₑ (⇒ᵢ [ g ]) (eᴸ₁ (⇒ₑ ax [ f ])))
  [ m⇐  f g ] = ⇒ᵢ (⇒ₑ (⇒ᵢ [ f ]) (eᴸ₁ (⇒ₑ ax [ g ])))
  [ r⇒⊗ f   ] = ⊗ₑᴸ₁ (eᴸ₁ (⇒ₑ [ f ] ax))
  [ r⇐⊗ f   ] = ⊗ₑᴸ₁ (    (⇒ₑ [ f ] ax))
  [ r⊗⇒ f   ] = ⇒ᵢ (    (⇒ₑ (⇒ᵢ [ f ]) (⊗ᵢ ax ax)))
  [ r⊗⇐ f   ] = ⇒ᵢ (eᴸ₁ (⇒ₑ (⇒ᵢ [ f ]) (⊗ᵢ ax ax)))
  [ m∘  f g ] = ⊗ₑᴸ₁ (⊗ᵢ [ f ] [ g ])
  [ m⇨  f g ] = ⇒ᵢ (⇒ₑ (⇒ᵢ [ g ]) (eᴸ₁ (⇒ₑ ax [ f ])))
  [ m⇦  f g ] = ⇒ᵢ (⇒ₑ (⇒ᵢ [ f ]) (eᴸ₁ (⇒ₑ ax [ g ])))
  [ r⇨∘ f   ] = ⊗ₑᴸ₁ (eᴸ₁ (⇒ₑ [ f ] ax))
  [ r⇦∘ f   ] = ⊗ₑᴸ₁ (    (⇒ₑ [ f ] ax))
  [ r∘⇨ f   ] = ⇒ᵢ (    (⇒ₑ (⇒ᵢ [ f ]) (⊗ᵢ ax ax)))
  [ r∘⇦ f   ] = ⇒ᵢ (eᴸ₁ (⇒ₑ (⇒ᵢ [ f ]) (⊗ᵢ ax ax)))
  [ mI      ] = ax
  [ mL      ] = ax
  [ mR      ] = ax
  [ Iᵢ  f   ] = ⊤ᵢ [ f ]
  [ Iₑ  f   ] = ⊤ₑ [ f ]
  [ Lᵢ  f   ] = ⊗ₑᴸ₁ (eᴸ₁ (⊗ₑᴸ₁ (⊗ₑᴸ₁ {!!})))
  [ Lₑ  f   ] = {!!}
  [ Rᵢ  f   ] = {!!}
  [ Rₑ  f   ] = {!!}

{-
private
  ⟦_⟧ᵀ : NLT.Type → ΛT.Type
  ⟦ el  A ⟧ᵀ = el  A
  ⟦ A ⊗ B ⟧ᵀ = ⟦ A ⟧ᵀ ⊗ ⟦ B ⟧ᵀ
  ⟦ A ⇒ B ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ
  ⟦ B ⇐ A ⟧ᵀ = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ








NLCL→LL : Translation NLT.Type ΛT.Type NLB.NL_ ΛB.Λ_
NLCL→LL = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
-}
