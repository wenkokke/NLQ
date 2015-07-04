------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------


module Logic.Classical.Ordered.LambekGrishin {ℓ} (Atom : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type Atom
     public hiding (module DecEq)
     public hiding ( ⇒-injective ; ⇐-injective ; ⊗-injective
                   ; ⇚-injective ; ⇛-injective ; ⊕-injective
                   ; ₀-injective ; ⁰-injective ; ₁-injective ; ¹-injective
                   )
open import Logic.Classical.Ordered.LambekGrishin.Structure.Polarised Atom
     public hiding ( module DecEq ; module Correct
                   ; ⇒-injective ; ⇐-injective ; ⊗-injective
                   ; ⇚-injective ; ⇛-injective ; ⊕-injective
                   ; ₀-injective ; ⁰-injective ; ₁-injective ; ¹-injective
                   )
open import Logic.Classical.Ordered.LambekGrishin.Judgement          Atom public
open import Logic.Classical.Ordered.LambekGrishin.Base               Atom public
open import Logic.Classical.Ordered.LambekGrishin.EquivalentToResMon Atom public
