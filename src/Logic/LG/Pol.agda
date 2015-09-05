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


module Logic.LG.Pol {ℓ} (Atom : Set ℓ) (Polarityᴬ? : Atom → Polarity)where


open import Logic.LG.Type.Polarised Atom Polarityᴬ? public
     hiding (module Correct; module Polarised; Polarised)

open import Logic.LG.Type Atom as Type public
     hiding ( ₀-injective ; ⁰-injective ; ₁-injective ; ¹-injective
     )

open import Logic.LG.Structure.Polarised Atom as Structure public
     hiding ( module DecEq
            ; ₀-injective ; ⁰-injective ; ₁-injective ; ¹-injective
     )

open import Logic.LG.Sequent Atom public
     hiding (module DecEq)

open import Logic.LG.Pol.Base Atom Polarityᴬ? public
