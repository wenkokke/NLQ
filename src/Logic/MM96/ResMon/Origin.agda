--------------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- This file was generated from:
--   src/Logic/LG/ResMon/Origin.agda
--------------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.MM96.ResMon.Origin {ℓ} (Atom : Set ℓ) where


import Logic.MM96.ResMon.Origin.El   ; module el = Logic.MM96.ResMon.Origin.El   Atom
import Logic.MM96.ResMon.Origin.Box  ; module ⟨l⟩  = Logic.MM96.ResMon.Origin.Box  Atom
import Logic.MM96.ResMon.Origin.Dia  ; module ⟨r⟩  = Logic.MM96.ResMon.Origin.Dia  Atom
import Logic.MM96.ResMon.Origin.Prod ; module ⊗  = Logic.MM96.ResMon.Origin.Prod Atom
import Logic.MM96.ResMon.Origin.ImpR ; module ⇒  = Logic.MM96.ResMon.Origin.ImpR Atom
import Logic.MM96.ResMon.Origin.ImpL ; module ⇐  = Logic.MM96.ResMon.Origin.ImpL Atom
import Logic.MM96.ResMon.Origin.Plug  ; module ⊙  = Logic.MM96.ResMon.Origin.Plug  Atom
import Logic.MM96.ResMon.Origin.CntL ; module ⇦  = Logic.MM96.ResMon.Origin.CntL Atom
import Logic.MM96.ResMon.Origin.CntR ; module ⇨  = Logic.MM96.ResMon.Origin.CntR Atom
