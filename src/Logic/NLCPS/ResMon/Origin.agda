--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Origin.agda
--------------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.NLCPS.ResMon.Origin {ℓ} (Atom : Set ℓ) where


import Logic.NLCPS.ResMon.Origin.El   ; module el = Logic.NLCPS.ResMon.Origin.El   Atom
import Logic.NLCPS.ResMon.Origin.Dia  ; module ◇₁ = Logic.NLCPS.ResMon.Origin.Dia  Atom
import Logic.NLCPS.ResMon.Origin.Dia2 ; module ◇₂ = Logic.NLCPS.ResMon.Origin.Dia2 Atom
import Logic.NLCPS.ResMon.Origin.Prod ; module ⊗  = Logic.NLCPS.ResMon.Origin.Prod Atom
import Logic.NLCPS.ResMon.Origin.ImpR ; module ⇒  = Logic.NLCPS.ResMon.Origin.ImpR Atom
import Logic.NLCPS.ResMon.Origin.ImpL ; module ⇐  = Logic.NLCPS.ResMon.Origin.ImpL Atom
