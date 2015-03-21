module Example where

import Base
import Match
import Prover
import LambekGrishin


sent :: Judgement Int
sent = index ("NP" ·⊗· "NP" ⇒ "S" ⊢ "S")

unifyFormula :: Formula String -> Formula String -> Maybe (Subst (Term Oper Name) String)
unifyFormula = unify

proofs :: [Proof]
proofs = search sent rules
