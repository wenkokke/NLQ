------------------------------------------------------------------------
-- The Lambek Calculus in Agda
--
-- Implements several views on proofs in the system ResMon which are
-- heavily used in the proof of admissibility of the transitivity rule.
--
-- One advantage of the residuation-monotonicity calculus is that
-- every connective *must* be introduced by an application of the
-- corresponding monotonicity-rule. The proofs in the `Origin` module
-- can be used to construct a view on a proof that makes this
-- introducing application of a monotonicity-rule explicit.
--
-- The proofs in this module are highly repetitive, and the decision
-- procedures and data structures could be abstracted over by
-- generalising over the connectives (cutting the file length by ±750
-- lines). However, I feel that abstracting over connectives would
-- make the logic a lot harder to read. I may do it in the future
-- anyway.
------------------------------------------------------------------------


open import Function                              using (id; flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)


module Logic.LG.ResMon.Origin {ℓ} (Atom : Set ℓ) where


import Logic.LG.ResMon.Origin.El   ; module el = Logic.LG.ResMon.Origin.El   Atom
import Logic.LG.ResMon.Origin.Box  ; module □  = Logic.LG.ResMon.Origin.Box  Atom
import Logic.LG.ResMon.Origin.Dia  ; module ◇  = Logic.LG.ResMon.Origin.Dia  Atom
import Logic.LG.ResMon.Origin.Sub0 ; module ₀  = Logic.LG.ResMon.Origin.Sub0 Atom
import Logic.LG.ResMon.Origin.Sup0 ; module ⁰  = Logic.LG.ResMon.Origin.Sup0 Atom
import Logic.LG.ResMon.Origin.Sub1 ; module ₁  = Logic.LG.ResMon.Origin.Sub1 Atom
import Logic.LG.ResMon.Origin.Sup1 ; module ¹  = Logic.LG.ResMon.Origin.Sup1 Atom
import Logic.LG.ResMon.Origin.Prod ; module ⊗  = Logic.LG.ResMon.Origin.Prod Atom
import Logic.LG.ResMon.Origin.ImpR ; module ⇒  = Logic.LG.ResMon.Origin.ImpR Atom
import Logic.LG.ResMon.Origin.ImpL ; module ⇐  = Logic.LG.ResMon.Origin.ImpL Atom
import Logic.LG.ResMon.Origin.Sum  ; module ⊕  = Logic.LG.ResMon.Origin.Sum  Atom
import Logic.LG.ResMon.Origin.SubL ; module ⇚  = Logic.LG.ResMon.Origin.SubL Atom
import Logic.LG.ResMon.Origin.SubR ; module ⇛  = Logic.LG.ResMon.Origin.SubR Atom
