module Prover.Example where

import Prover.Base
import Prover.Prover
import Prover.LambekGrishin


sent :: Judgement String
sent = john ·⊗· loves ·⊗· someone ⊢ ["S"]

proofs :: [Proof]
proofs = search (index sent) rules
