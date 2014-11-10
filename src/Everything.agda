------------------------------------------------------------------------
-- The Lambek Calculus in Agda
------------------------------------------------------------------------

module Everything where

-- Definitions categories and functors.
import Categories

import Logic.Lambek.Judgement

import Logic.Lambek.Judgement.Context

import Logic.Lambek.Judgement.Context.Polarised

import Logic.Lambek.ResMon.Base

import Logic.Lambek.ResMon.Derivation

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

import Logic.Lambek.Type

import Logic.Lambek.Type.Context

import Logic.Lambek.Type.Context.Polarised

import Logic.LambekGrishin.Judgement

import Logic.LambekGrishin.Judgement.Context

import Logic.LambekGrishin.Judgement.Context.Polarised

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

import Logic.LambekGrishin.Type.Context

import Logic.LambekGrishin.Type.Context.Polarised

import Logic.LambekGrishin.Type.Polarised

import Logic.Polarity

import Logic.Reification
