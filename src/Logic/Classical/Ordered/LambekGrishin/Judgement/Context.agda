------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
------------------------------------------------------------------------


open import Categories.Category                        using (Category)
open import Algebra                                    using (module Monoid; Monoid)
open import Function                                   using (id; _∘_)
open import Data.Empty                                 using (⊥)
open import Data.Product                               using (_×_; _,_; proj₁; proj₂)
open import Data.Unit                                  using (⊤; tt)
open import Relation.Nullary                           using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)


module Logic.Classical.Ordered.LambekGrishin.Judgement.Context {ℓ} (Univ : Set ℓ) where


open import Logic.Classical.Ordered.LambekGrishin.Type         Univ as T
open import Logic.Classical.Ordered.LambekGrishin.Type.Context Univ as TC hiding (module Simple; module Context; Context)
open import Logic.Classical.Ordered.LambekGrishin.Judgement    Univ

