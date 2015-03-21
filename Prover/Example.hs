module Prover.Example where

import Prover.Base
import Prover.Prover
import Prover.LambekGrishin


sent :: Judgement String
sent = john ·⊗· thinks ·⊗· mary ·⊗· left ⊢ ["S"]

proofs :: [Proof]
proofs = iddfs (solve maxBound (index sent) rules)
