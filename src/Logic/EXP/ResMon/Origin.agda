--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Origin.agda
--------------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.EXP.ResMon.Origin {ℓ} (Atom : Set ℓ) where


import Logic.EXP.ResMon.Origin.El   ; module el = Logic.EXP.ResMon.Origin.El   Atom
import Logic.EXP.ResMon.Origin.Dia  ; module ◇₁ = Logic.EXP.ResMon.Origin.Dia  Atom
import Logic.EXP.ResMon.Origin.Dia2 ; module ◇₂ = Logic.EXP.ResMon.Origin.Dia2 Atom
import Logic.EXP.ResMon.Origin.Prod ; module ⊗  = Logic.EXP.ResMon.Origin.Prod Atom
import Logic.EXP.ResMon.Origin.ImpR ; module ⇒  = Logic.EXP.ResMon.Origin.ImpR Atom
import Logic.EXP.ResMon.Origin.ImpL ; module ⇐  = Logic.EXP.ResMon.Origin.ImpL Atom
