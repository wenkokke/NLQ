------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

module Everything where

-- Defines a residuated algebra, which I've taken to be:
--
-- (1) a residuated ordered monoid without associativity, or
-- (2) an algebra which adds a partial order and a left and right
--     residuation operation. Congruence of the binary operator ∙
--     results from its compatibility with the partial order ≤.
--
import Algebra.ResiduatedAlgebra

-- Definitions categories and functors.
import Categories

import Logic.Lambek.ResMon.Base

import Logic.Lambek.ResMon.Complete

-- Implements derivations---also known as partial proofs or term
-- contexts---which are generally written as:
--
--     A ⊢ B
--     -----
--       ⋮
--     -----
--     C ⊢ D
--
-- This definition guarantees that there is exactly *one* sub-proof
-- missing. In addition, this module provides proofs that these
-- contexts form a category, and thus behave function-like.
import Logic.Lambek.ResMon.Derivation

import Logic.Lambek.ResMon.Judgement

import Logic.Lambek.ResMon.Judgement.Context

import Logic.Lambek.ResMon.Judgement.Context.Polarised

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
import Logic.Lambek.ResMon.Origin

import Logic.Lambek.ResMon.Trans

-- Implements the axioms and some derived inference rules.
import Logic.Lambek.SC.Base

import Logic.Lambek.SC.Complete

-- Implements a proof of equivalence with the residuation-monotonicity
-- calculus as `ResMon⇔SC`.
import Logic.Lambek.SC.EquivalentToResMon

-- Implements the axioms and some derived inference rules.
import Logic.Lambek.SC.Judgement

-- Uses the equivalence relation between SC and the
-- residuation-monotonicity axiomatisations to import the proof of
-- transitivity into SC.
import Logic.Lambek.SC.Trans

import Logic.Lambek.Type

import Logic.Lambek.Type.Complexity

import Logic.Lambek.Type.Context

import Logic.Lambek.Type.Context.Polarised

import Logic.LambekGrishin.ResMon.Base

-- Implements derivations---also known as partial proofs or term
-- contexts---which are generally written as:
--
--     A ⊢ B
--     -----
--       ⋮
--     -----
--     C ⊢ D
--
-- This definition guarantees that there is exactly *one* sub-proof
-- missing. In addition, this module provides proofs that these
-- contexts form a category, and thus behave function-like.
import Logic.LambekGrishin.ResMon.Derivation

import Logic.LambekGrishin.ResMon.Judgement

import Logic.LambekGrishin.ResMon.Judgement.Context

import Logic.LambekGrishin.ResMon.Judgement.Context.Polarised

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
import Logic.LambekGrishin.ResMon.Origin

import Logic.LambekGrishin.ResMon.Trans

import Logic.LambekGrishin.Type

import Logic.LambekGrishin.Type.Complexity

import Logic.LambekGrishin.Type.Context

import Logic.LambekGrishin.Type.Context.Polarised

import Logic.LambekGrishin.Type.Polarised

import Logic.Polarity

import Logic.Reification

-- A utility module which constructs an equivalence relation from a
-- partial order. This requires some tricks, as the Agda standard
-- library defines orders based on equivalences. Therefore, instead of
-- requiring an instance of the poset class, this module requires an
-- order together with proof of identity and transitivity, and defines
-- an equivalence relation, and a complete instance of the poset class.
import Relation.Binary.PartialOrderToEquivalence
