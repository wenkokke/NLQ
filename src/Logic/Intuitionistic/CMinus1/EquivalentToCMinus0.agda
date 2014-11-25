------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------

open import Algebra using (module Monoid)
open import Data.Bool using (Bool; true; false)
open import Data.List as List using (map; partition)
open import Data.List.Properties using (map-++-commute)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym)


module Logic.Intuitionistic.CMinus1.EquivalentToCMinus0 {ℓ} (Univ : Set ℓ) (⫫ : Univ) where


open import Logic.Intuitionistic.Type              Univ
open import Logic.Intuitionistic.Structure         Type
open import Logic.Intuitionistic.CMinus0.Judgement Univ   renaming (Judgement to Judgement₀)
open import Logic.Intuitionistic.CMinus0.Base      Univ ⫫ renaming (λC⁻_ to λC⁻₀_)
open import Logic.Intuitionistic.CMinus1.Judgement Univ   renaming (Judgement to Judgement₁)
open import Logic.Intuitionistic.CMinus1.Base      Univ ⫫ renaming (λC⁻_ to λC⁻₁_)
open import Relation.Binary.EqReasoning (P.setoid (List Type))
open Monoid (List.monoid Type) using (assoc)


¬_ : Type → Type
¬ A = A ⇒ el ⫫


is-¬? : Type → Bool
is-¬? (_ ⇒ el ⫫) = true
is-¬?  _         = false


⟦_⟧₀¹ : Judgement₀ → Judgement₁
⟦ Γ ⊢ A ⟧₀¹ with (partition is-¬? Γ)
⟦ _ ⊢ A ⟧₀¹ | (Δ , Γ) = Γ ⊢ A ∣ Δ


⟦_⟧₁⁰ : Judgement₁ → Judgement₀
⟦ Γ ⊢ A ∣ Δ ⟧₁⁰ = Γ ++ (map ¬_ Δ) ⊢ A


-- lemma which shows how to translate binary rules from  λC⁻₁ to λC⁻₀.
private
  lem-⟦_⟧₁⁰ : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A}
            → λC⁻₀ (Γ₁ ++ map ¬_ Δ₁) ++ (Γ₂ ++ map ¬_ Δ₂) ⊢ A
            → λC⁻₀ (Γ₁ ++ Γ₂) ++ (map ¬_ (Δ₁ ++ Δ₂)) ⊢ A
  lem-⟦_⟧₁⁰ {Γ₁} {Δ₁} {Γ₂} {Δ₂}
    rewrite map-++-commute ¬_ Δ₁ Δ₂ = exch Γ₁ Γ₂ (map ¬_ Δ₁) (map ¬_ Δ₂)


⇒e′ : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B}
    → λC⁻₀  Γ₁        ++ map ¬_  Δ₁        ⊢ A ⇒ B
    → λC⁻₀        Γ₂  ++ map ¬_        Δ₂  ⊢ A
    → λC⁻₀ (Γ₁ ++ Γ₂) ++ map ¬_ (Δ₁ ++ Δ₂) ⊢ B
⇒e′ {Γ₁} {Δ₁} f g = lem-⟦_⟧₁⁰ {Γ₁} {Δ₁} (⇒e f g)




from : {J : Judgement₁} → λC⁻₁ J → λC⁻₀ ⟦ J ⟧₁⁰
from id                                   = id
from (⇒i f)                               = ⇒i (from f)
from (⇒e {Γ₁} {Δ₁} {Γ₂} {Δ₂} f g)         = ⇒e′ {Γ₁} {Δ₁} (from f) (from g)
from (⇛i {Γ₁} {Δ₁} {Γ₂} {Δ₂} f g)         = lem-⟦_⟧₁⁰ {Γ₁} {Δ₁} (⇛i (from f) (from g))
from (⇛e {Γ₁} {Δ₁} {Γ₂} {Δ₂} {A} {B} f g) = lem-⟦_⟧₁⁰ {Γ₁} {Δ₁} (⇛e (from f) (exch (A , ∅) (¬ B , ∅) Γ₂ (map ¬_ Δ₂) (from g)))
from (raa {Γ} {Δ} {A} f)                  = raa (exch ∅ (¬ A , ∅) Γ (map ¬_ Δ) (from f))
from (⇒ke {Γ} {Δ} {A} f)                  = exch ∅ Γ (¬ A , ∅) (map ¬_ Δ) (⇒ke (exch ∅ (¬ A , ∅) Γ (map ¬_ Δ) (from f)))
from (contl {Γ} {Δ} f)                    = cont (from f)
from (contr {Γ} {Δ} f)                    = ++-comm Γ (map ¬_ (_ , Δ)) (cont (++-comm (map ¬_ (_ , (_ , Δ))) Γ (from f)))
from (weakl {Γ₁} Γ₂ {Δ} f)                = XZY→XYZ Γ₁ Γ₂ (map ¬_ Δ) (weak Γ₂ (from f))
from (weakr {Γ} {Δ₁} Δ₂ f)
         rewrite map-++-commute ¬_ Δ₁ Δ₂
               | sym (assoc Γ (map ¬_ Δ₁) (map ¬_ Δ₂))
               = weak (map ¬_ Δ₂) (from f)

from (exchl Γ₁ Γ₂ Γ₃ Γ₄ {Δ} {A} f) = lem₂
  where
    lem₁ : λC⁻₀ (Γ₁ ++ Γ₃) ++ (Γ₂ ++ (Γ₄ ++ map ¬_ Δ)) ⊢ A
    lem₁ rewrite sym (assoc             Γ₂    Γ₄  (map ¬_ Δ))
               | sym (assoc (Γ₁ ++ Γ₃) (Γ₂ ++ Γ₄) (map ¬_ Δ)) = from f
    lem₂ : λC⁻₀ ((Γ₁ ++ Γ₂) ++ (Γ₃ ++ Γ₄)) ++ map ¬_ Δ ⊢ A
    lem₂ rewrite assoc (Γ₁ ++ Γ₂) (Γ₃ ++ Γ₄) (map ¬_ Δ)
               | assoc             Γ₃    Γ₄  (map ¬_ Δ)
               = exch Γ₁ Γ₂ Γ₃ (Γ₄ ++ map ¬_ Δ) lem₁

from (exchr {Γ} Δ₁ Δ₂ Δ₃ Δ₄ {A} f) = lem₂
  where
    lem₁ : λC⁻₀ ((Γ ++ map ¬_ Δ₁) ++ map ¬_ Δ₃) ++ (map ¬_ Δ₂ ++ map ¬_ Δ₄) ⊢ A
    lem₁ rewrite assoc Γ (map ¬_ Δ₁)  (map ¬_ Δ₃)
               | assoc Γ (map ¬_ Δ₁ ++ map ¬_ Δ₃) (map ¬_ Δ₂ ++ map ¬_ Δ₄)
               | sym (map-++-commute ¬_  Δ₁    Δ₃            )
               | sym (map-++-commute ¬_             Δ₂    Δ₄ )
               | sym (map-++-commute ¬_ (Δ₁ ++ Δ₃) (Δ₂ ++ Δ₄)) = from f
    lem₂ : λC⁻₀ Γ ++ (map ¬_ ((Δ₁ ++ Δ₂) ++ (Δ₃ ++ Δ₄))) ⊢ A
    lem₂ rewrite map-++-commute ¬_ (Δ₁ ++ Δ₂) (Δ₃ ++ Δ₄)
               | map-++-commute ¬_  Δ₁    Δ₂
               | map-++-commute ¬_             Δ₃    Δ₄
               | sym (assoc Γ (map ¬_ Δ₁ ++ map ¬_ Δ₂) (map ¬_ Δ₃ ++ map ¬_ Δ₄))
               | sym (assoc Γ (map ¬_ Δ₁)  (map ¬_ Δ₂))
               = exch (Γ ++ map ¬_ Δ₁) (map ¬_ Δ₂) (map ¬_ Δ₃) (map ¬_ Δ₄) lem₁

to : {J : Judgement₀} → λC⁻₀ J → λC⁻₁ ⟦ J ⟧₀¹
to f = {!!}
