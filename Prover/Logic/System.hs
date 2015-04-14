{-# LANGUAGE ViewPatterns #-}
module Logic.System where


import Prelude hiding (exp)
import Data.Char (toUpper)

import Prover
import Logic.Base (ConId(..))
import Logic.Rules

-- |Enumeration representing all supported logical systems.
data System = NL | NLCL | CNL | LG | FNL | FCNL | FLG | EXP
            deriving (Eq,Show)

-- |Parse a string into a logical system.
parseSystem :: String -> System
parseSystem (map toUpper -> "NL")   = NL
parseSystem (map toUpper -> "NLCL") = NLCL
parseSystem (map toUpper -> "CNL")  = CNL
parseSystem (map toUpper -> "LG")   = LG
parseSystem (map toUpper -> "FNL")  = FNL
parseSystem (map toUpper -> "FCNL") = FCNL
parseSystem (map toUpper -> "FLG")  = FLG
parseSystem (map toUpper -> "EXP")  = EXP
parseSystem str = error ("Error: Unknown logical system `"++str++"'.")

-- |Return the inference rules associated with a logical system.
getRules :: System -> [Rule ConId Int]
getRules NL   = nl
getRules NLCL = nlcl
getRules FNL  = fnl
getRules CNL  = cnl
getRules FCNL = fcnl
getRules LG   = lg
getRules FLG  = flg
getRules EXP  = exp

-- |Return the sequent that corresponds to this logical system.
getSetup :: System -> (Maybe ConId, ConId, Maybe ConId, ConId)
getSetup NLCL = (Nothing  , FProd, Nothing  , JForm  )
getSetup _    = (Just SDia, SProd, Just Down, JFocusR)
