------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


open import Level                                      using (suc; _⊔_)
open import Function                                   using (id; _∘_)
open import Function.Equivalence                       using (_⇔_; equivalence)
open import Data.Product                               using (_×_; proj₁)
open import Relation.Nullary                           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable                 using (fromWitness)
open import Relation.Binary.PropositionalEquality as P using (_≡_)


open import Logic.Polarity
open import Logic.Translation


module Logic.Classical.Ordered.LambekGrishin.FocPol {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type.Polarised (Polarity × Atom) proj₁
     public hiding (module Correct; module Polarised; Polarised)

open import Logic.Classical.Ordered.LambekGrishin.Type (Polarity × Atom) as Type
     public hiding ( ⇒-injective ; ⇐-injective ; ⊗-injective

                   ; ⇚-injective ; ⇛-injective ; ⊕-injective

                   ; ₀-injective ; ⁰-injective ; ₁-injective ; ¹-injective

            )

open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised (Polarity × Atom) as Structure
     public hiding ( module DecEq

                   ; ⇒-injective ; ⇐-injective ; ⊗-injective

                   ; ⇚-injective ; ⇛-injective ; ⊕-injective

                   ; ₀-injective ; ⁰-injective ; ₁-injective ; ¹-injective

            )

open import Logic.Classical.Ordered.LambekGrishin.Judgement (Polarity × Atom)
     public hiding (module DecEq)

open import Logic.Classical.Ordered.LambekGrishin.FocPol.Base Atom
     public
