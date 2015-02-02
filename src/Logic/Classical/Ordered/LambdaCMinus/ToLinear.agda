open import Algebra                               using (module Monoid)
open import Function                              using (_$_)
open import Data.List                             using (List; map; _++_) renaming ([] to ∅; _∷_ to _,_)
open import Data.Product                          using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; subst)


module Logic.Classical.Ordered.LambdaCMinus.ToLinear {ℓ} (Univ : Set ℓ) where


open import Logic.Type                                Univ
open import Logic.Index
open import Logic.Translation                         Univ 
open import Logic.Structure.Conjunction               Univ renaming (_[_] to _⟨_⟩)
open import Logic.Classical.Judgement Conjunction Type (List Type) as OJ using (Judgement)
open import Logic.Classical.Judgement (List Type) Type (List Type) as LJ
open import Logic.Classical.Ordered.LambdaCMinus.Base Univ as O
open import Logic.Classical.Linear.LambdaCMinus.Base  Univ as L
open Monoid (Data.List.monoid Type) using (assoc; identity)



private
  ⟦_⟧ᵀ : Type → Type
  ⟦_⟧ᵀ (el  A) = el A
  ⟦_⟧ᵀ (A ⇒ B) = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ 
  ⟦_⟧ᵀ (B ⇐ A) = ⟦ A ⟧ᵀ ⇒ ⟦ B ⟧ᵀ 
  ⟦_⟧ᵀ (B ⇚ A) = ⟦ B ⟧ᵀ ⇚ ⟦ A ⟧ᵀ   
  ⟦_⟧ᵀ (A ⇛ B) = ⟦ B ⟧ᵀ ⇚ ⟦ A ⟧ᵀ   
  ⟦_⟧ᵀ (A ⊗ B) = ⟦ A ⟧ᵀ ⊗ ⟦ B ⟧ᵀ 
  ⟦_⟧ᵀ (A ⊕ B) = ⟦ A ⟧ᵀ ⊕ ⟦ B ⟧ᵀ 

  ⟦_⟧⁺ : Conjunction → List Type
  ⟦_⟧⁺ (· A ·) = ⟦ A ⟧ᵀ , ∅
  ⟦_⟧⁺ (Γ ⊗ Δ) = ⟦ Γ ⟧⁺ ++ ⟦ Δ ⟧⁺

  ⟦_⟧⁻ : List Type → List Type
  ⟦_⟧⁻ = map ⟦_⟧ᵀ

  ⟦_⟧ᴶ : OJ.Judgement → LJ.Judgement
  ⟦_⟧ᴶ (Γ OJ.⊢      Δ) = ⟦ Γ ⟧⁺ ⊢          ⟦ Δ ⟧⁻
  ⟦_⟧ᴶ (Γ OJ.⊢[ A ] Δ) = ⟦ Γ ⟧⁺ ⊢[ ⟦ A ⟧ᵀ ] ⟦ Δ ⟧⁻


  [_] : ∀ {J} → O.λC⁻ J → L.λC⁻ ⟦ J ⟧ᴶ
  [ O.ax                          ] = L.ax
  [ O.⇒ᵢ                      f   ] = L.⇒ᵢ [ f ]
  [ O.⇒ₑ  {Γ₁ = Γ₁}           f g ] = L.sᴸ ⟦ Γ₁ ⟧⁺ $ L.⇒ₑ [ g ] [ f ]
  [ O.⇐ᵢ  {A = A}             f   ] = L.⇒ᵢ $ L.sᴸ ⟦ · A · ⟧⁺ [ f ]
  [ O.⇐ₑ                      f g ] = L.⇒ₑ [ f ] [ g ]
  [ O.raa                     f   ] = L.raa [ f ]
  [ O.⇒ₑᵏ {Δ = Δ}             α f ] with map-lookup Δ α
  [ O.⇒ₑᵏ {Γ} {Δ}             α f ] | β , p = L.⇒ₑᵏ β $ subst (λ A → L.λC⁻ ⟦ Γ ⟧⁺ ⊢[ A ] ⟦ Δ ⟧⁻) p [ f ]
  [ O.-ᵢ₀ {Δ = Δ}             α f ] with map-lookup {f = ⟦_⟧ᵀ} Δ α
  [ O.-ᵢ₀ {Γ} {A} {Δ}         α f ] | β , p = ∅ₑ $ L.-ᵢ [ f ] $ subst (λ A → L.λC⁻ A , ∅ ⊢ ⟦ Δ ⟧⁻) (sym p) $ ⇒ₑᵏ β ax
  [ O.-ᵢ₂ {Γ₁} {B = B}        f g ] = L.sᴸ ⟦ Γ₁ ⟧⁺ $ L.-ᵢ [ f ] $ L.sᴸ′ ⟦ · B · ⟧⁺ $ [ g ]
  [ O.-ᵢ₁                     f g ] = L.-ᵢ [ f ] [ g ]
  [ O.-ₑ₀ {Δ = Δ}             α f ] = ∅ₑ (L.-ₑ [ f ] ax)
  [ O.-ₑ₂ {Γ₁} {A = A}        f g ] = L.sᴸ ⟦ Γ₁ ⟧⁺ $ L.-ₑ [ g ] $ L.sᴸ  ⟦ · A · ⟧⁺ $ [ f ]
  [ O.-ₑ₁                     f g ] = L.-ₑ [ f ] [ g ]
  [ O.⊗ᵢ                      f g ] = L.⊗ᵢ [ f ] [ g ]
  [ O.⊗ₑ  {Γ₁} Γ₂ {A} {B} {C} f g ] = ∅ₑ $ lem-⊗ₑ Γ₂ {C = C} [ f ] $ ∅ᵢ $ [ g ]
    where
    lem-⊗ₑ : ∀ {Γ₁ : Conjunction} (Γ₂ : Context) {Γ₃ : List Type} {A B C Δ}
           → L.λC⁻ (⟦ Γ₁ ⟧⁺)                           ⊢[ ⟦ A ⊗ B ⟧ᵀ ] (⟦ Δ ⟧⁻)
           → L.λC⁻ (⟦ (Γ₂ ⟨ · A · ⊗ · B · ⟩) ⟧⁺) ++ Γ₃ ⊢[ ⟦ C     ⟧ᵀ ] (⟦ Δ ⟧⁻)
           → L.λC⁻ (⟦ (Γ₂ ⟨ Γ₁ ⟩) ⟧⁺)            ++ Γ₃ ⊢[ ⟦ C     ⟧ᵀ ] (⟦ Δ ⟧⁻)
    lem-⊗ₑ [] f g = L.⊗ₑ f g
    lem-⊗ₑ {Γ₁} (Γ₂ ⊗> Γ₃) {Γ₄} {A} {B} {C} {Δ} f g
            rewrite assoc  (⟦ Γ₂ ⟧⁺) (⟦ Γ₃ ⟨       Γ₁      ⟩ ⟧⁺) Γ₄
                  | assoc  (⟦ Γ₂ ⟧⁺) (⟦ Γ₃ ⟨ · A · ⊗ · B · ⟩ ⟧⁺) Γ₄
                  = L.eᴸ ∅ (⟦ Γ₂ ⟧⁺) (⟦ Γ₃ ⟨ Γ₁ ⟩ ⟧⁺) Γ₄
                  $ lem-⊗ₑ {Γ₁} Γ₃ {⟦ Γ₂ ⟧⁺ ++ Γ₄} {A} {B} {C} {Δ} f
                  $ L.eᴸ ∅ (⟦ Γ₃ ⟨ · A · ⊗ · B · ⟩ ⟧⁺) (⟦ Γ₂ ⟧⁺) Γ₄
                  $ g             
    lem-⊗ₑ {Γ₁} (Γ₂ <⊗ Γ₃) {Γ₄} {A} {B} {C} {Δ} f g
            rewrite assoc (⟦ Γ₂ ⟨       Γ₁      ⟩ ⟧⁺) (⟦ Γ₃ ⟧⁺) Γ₄
                  | assoc (⟦ Γ₂ ⟨ · A · ⊗ · B · ⟩ ⟧⁺) (⟦ Γ₃ ⟧⁺) Γ₄
                  = lem-⊗ₑ {Γ₁} Γ₂ {⟦ Γ₃ ⟧⁺ ++ Γ₄} {A} {B} {C} {Δ} f g


Ord→Lin : Translation Type O.λC⁻_ L.λC⁻_
Ord→Lin = record { ⟦_⟧ᵀ = ⟦_⟧ᵀ ; ⟦_⟧ᴶ = ⟦_⟧ᴶ ; [_] = [_] }
