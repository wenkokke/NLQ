------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

open import Function                                   using (_∘_)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary                            using (DecSetoid)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module TypeAndEffect.Type {ℓ} (Univ : Set ℓ) where


infixr 20 _^_⇒_^_


data Type : Set ℓ where

  el : Univ → Type

  _^_⇒_^_ : Type → Type → Type → Type → Type


-- Proofs which show that constructors of types (as all Agda
-- data-constructors) respect equality.

el-injective : ∀ {A B} → el A ≡ el B → A ≡ B
el-injective refl = refl


^⇒^-injective : ∀ {A₁ B₁ T₁ U₁ A₂ B₂ T₂ U₂}
              → (A₁ ^ U₁ ⇒ B₁ ^ T₁) ≡ (A₂ ^ U₂ ⇒ B₂ ^ T₂)
              → (A₁ ≡ A₂ × U₁ ≡ U₂) × (B₁ ≡ B₂ × T₁ ≡ T₂)
^⇒^-injective refl = (refl , refl) , (refl , refl)
