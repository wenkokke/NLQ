module Prover.LambekGrishin.Lexicon where


import Prover.Base
import Prover.LambekGrishin.Base
import Prover.LambekGrishin.Rules


item :: String -> Formula String
item = toFormula


unicorn  = item "N"
teacher  = item "N"

nice     = "N" ⇐ "N"
old      = "N" ⇐ "N"

john     = item "NP"
mary     = item "NP"
bill     = item "NP"

smiles   = "NP" ⇒ "S"
left     = "NP" ⇒ "S"
cheats   = "NP" ⇒ "S"

teases   = ("NP" ⇒ "S") ⇐ "NP"
loves    = ("NP" ⇒ "S") ⇐ "NP"
thinks   = ("NP" ⇒ "S") ⇐ "S"

everyone = ("NP" ⇐ "N") ⊗ "N"
someone  = ("NP" ⇐ "N") ⊗ "N"
