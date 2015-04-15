{-# LANGUAGE ViewPatterns #-}
module Logic.System where


import Prelude hiding (exp)
import Data.Char (toUpper)

import Prover
import Logic.Base (ConId(..))
import Logic.Rules

-- |Enumeration representing all supported logical systems.
data System = NL | CNL | LG | FNL | FCNL | FLG | EXP
            | AlgNL | AlgNLCL
            deriving (Eq,Show)

data SysDescr = SysDescr
  { unaryOp  :: Maybe ConId
  , binaryOp :: ConId
  , down     :: Maybe ConId
  , sequent  :: ConId
  , rules    :: [Rule ConId Int]
  , finite   :: Bool
  }

-- |Parse a string into a logical system.
parseSystem :: String -> System
parseSystem (map toUpper -> "NL")      = NL
parseSystem (map toUpper -> "CNL")     = CNL
parseSystem (map toUpper -> "LG")      = LG
parseSystem (map toUpper -> "FNL")     = FNL
parseSystem (map toUpper -> "FCNL")    = FCNL
parseSystem (map toUpper -> "FLG")     = FLG
parseSystem (map toUpper -> "EXP")     = EXP
parseSystem (map toUpper -> "ALGNL")   = AlgNL
parseSystem (map toUpper -> "ALGNLCL") = AlgNLCL
parseSystem str = error ("Error: Unknown logical system `"++str++"'.")

-- |Return the inference rules associated with a logical system.
getRules :: System -> [Rule ConId Int]
getRules    NL   = nl
getRules    FNL  = fnl
getRules    CNL  = cnl
getRules    FCNL = fcnl
getRules    LG   = lg
getRules    FLG  = flg
getRules    EXP  = exp
getRules AlgNL   = algnl
getRules AlgNLCL = algnlcl

-- |Return the sequent that corresponds to this logical system.
getSysDescr :: System -> SysDescr
getSysDescr AlgNL   = SysDescr Nothing FProd Nothing JForm algnl   True
getSysDescr AlgNLCL = SysDescr Nothing FProd Nothing JForm algnlcl False
getSysDescr sys     = SysDescr (Just SDia) SProd (Just Down) JFocusR (getRules sys) True
