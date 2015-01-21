open import Algebra                               using (module Monoid)
open import Data.Fin                              using (Fin; suc; zero; #_)
open import Data.List    as List                  using (List; length; _++_) renaming ([] to ·; _∷_ to _,_; _∷ʳ_ to _,ʳ_)
open import Data.Product                          using (Σ; Σ-syntax; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)


module AHS.Equivalence {ℓ₁} (Univ : Set ℓ₁) where


open import AHS.Type Univ
open import AHS.Explicit Univ as E using ()
open import AHS.Implicit Univ as I using ()
open Monoid (List.monoid Type) using (identity)


from : ∀ {J} → E.AHS J → I.AHS J
from (E.ax                   ) = I.ax   (# 0)
from (E.⇒ᵢ               f   ) = I.⇒ᵢ   (from f)
from (E.⇒ₑ  {Γ₁} {Γ₂}    f g ) = I.⇒ₑ   (I.sᴸ Γ₁ Γ₂ (I.wᴸ Γ₂ (from f))) (I.wᴸ Γ₁ (from g))
from (E.raa              f   ) = I.raa  (from f)
from (E.⇒ₑᵏ              f   ) = I.⇒ₑᵏ  (# 0) (from f)
from (E.-ᵢ  {Γ₁} {Γ₂}    f g ) = I.-ᵢ   (I.sᴸ Γ₁ Γ₂ (I.wᴸ Γ₂ (from f))) (I.eᴸ′ · (_ , ·) Γ₁ Γ₂ (I.wᴸ′ Γ₁ (from g)))
from (E.-ₑ  {Γ₁} {Γ₂}    f g ) = I.-ₑ   (I.sᴸ Γ₁ Γ₂ (I.wᴸ Γ₂ (from f))) (I.eᴸ  · (_ , ·) Γ₁ Γ₂ (I.wᴸ  Γ₁ (from g)))
from (E.⊗ᵢ  {Γ₁} {Γ₂}    f g ) = I.⊗ᵢ   (I.sᴸ Γ₁ Γ₂ (I.wᴸ Γ₂ (from f))) (I.wᴸ Γ₁ (from g))
from (E.⊗ₑ  {Γ₁} {Γ₂}    f g ) = I.⊗ₑ   (I.sᴸ Γ₁ Γ₂ (I.wᴸ Γ₂ (from f))) (I.eᴸ  · (_ , (_ , ·)) Γ₁ Γ₂ (I.wᴸ Γ₁ (from g)))
from (E.eᴸ  Γ₁ Γ₂ Γ₃ Γ₄  f   ) = I.eᴸ   Γ₁ Γ₂ Γ₃ Γ₄ (from f)
from (E.eᴸ′ Γ₁ Γ₂ Γ₃ Γ₄  f   ) = I.eᴸ′  Γ₁ Γ₂ Γ₃ Γ₄ (from f)
from (E.cᴸ₁              f   ) = I.cᴸ₁  (from f)
from (E.cᴸ₁′             f   ) = I.cᴸ₁′ (from f)
from (E.wᴸ₁              f   ) = I.wᴸ₁  (from f)
from (E.wᴸ₁′             f   ) = I.wᴸ₁′ (from f)
from (E.eᴿ  Δ₁ Δ₂ Δ₃ Δ₄  f   ) = I.eᴿ   Δ₁ Δ₂ Δ₃ Δ₄ (from f)   
from (E.eᴿ′ Δ₁ Δ₂ Δ₃ Δ₄  f   ) = I.eᴿ′  Δ₁ Δ₂ Δ₃ Δ₄ (from f)


private
  lem-cᴸ-· : ∀ {Γ A Δ} → E.AHS Γ ++ Γ ⊢[ A ] Δ → E.AHS Γ ⊢[ A ] Δ
  lem-cᴸ-· {Γ} = subst (λ Γ′ → E.AHS Γ ++ Γ′ ⊢[ _ ] _ → E.AHS Γ′ ⊢[ _ ] _) (proj₂ identity Γ) (E.cᴸ Γ ·)


to : ∀ {J} → I.AHS J → E.AHS J
to (I.ax  x   ) = E.ax′ x
to (I.⇒ᵢ  f   ) = E.⇒ᵢ (to f)
to (I.⇒ₑ  f g ) = lem-cᴸ-· (E.⇒ₑ (to f) (to g))
to (I.raa f   ) = E.raa (to f)
to (I.⇒ₑᵏ α f ) = E.⇒ₑᵏ′ α (to f)
to (I.-ᵢ  f g ) = lem-cᴸ-· (E.-ᵢ (to f) (to g))
to (I.-ₑ  f g ) = lem-cᴸ-· (E.-ₑ (to f) (to g))
to (I.⊗ᵢ  f g ) = lem-cᴸ-· (E.⊗ᵢ (to f) (to g))
to (I.⊗ₑ  f g ) = lem-cᴸ-· (E.⊗ₑ (to f) (to g))
