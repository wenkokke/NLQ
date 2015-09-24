--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--------------------------------------------------------------------------------


open import Function using (_∘_)
open import Data.Product using (∃; _×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)


module Logic.NLP.SC.Base {ℓ} (Atom : Set ℓ) where


open import Logic.NLP.SC.Type              Atom
open import Logic.NLP.SC.Structure         Atom
open import Logic.NLP.SC.Structure.Context Atom
open import Logic.NLP.SC.Sequent           Atom


infix 1 NL_ _⊢NL_
mutual
  _⊢NL_ : Structure → Type → Set ℓ
  Γ ⊢NL B = NL Γ ⊢ B

  data NL_ : Sequent → Set ℓ where

    ax : ∀ {A} → · A · ⊢NL A

    ⇒L : ∀ (Δ : Context) {Γ A B C}
       → Γ ⊢NL A → Δ [ · B · ] ⊢NL C → Δ [ Γ ∙ · A ⇒ B · ] ⊢NL C

    ⇒R : ∀ {Γ A B} → · A · ∙ Γ ⊢NL B → Γ ⊢NL A ⇒ B

    ⇐L : ∀ (Δ : Context) {Γ A B C}
       → Γ ⊢NL A → Δ [ · B · ] ⊢NL C → Δ [ · B ⇐ A · ∙ Γ ] ⊢NL C

    ⇐R : ∀ {Γ A B} → Γ ∙ · A · ⊢NL B → Γ ⊢NL B ⇐ A
