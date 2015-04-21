{-# LANGUAGE ViewPatterns #-}
module Logic.System (System(..),SysDescr(..),parseSystem,getRules,getSysDescr)where


import Prelude hiding (exp)
import Data.Char (toUpper)

import Logic.Base
import Logic.Rules

-- |Enumeration representing all supported logical systems.
data System
  = ALGNL   -- ^ algebraic non-associative Lambek calculus
  | ALGNLCL -- ^ algebraic Lambek calculus (by Barker & Shan)
  | ALGEXP  -- ^ algebraic experimental Lambek calculus (with "reset")

  | STRNL   -- ^ structured non-associative Lambek calculus
  | STRCNL  -- ^ structured classical non-associative Lambek calculus
  | STRLG   -- ^ structured Lambek-Grishin

  | POLNL   -- ^ polarised non-associative Lambek calculus (extracted from FLG)
  | POLCNL  -- ^ polarised classical non-associative Lambek calculus (extracted from FLG)
  | POLLG   -- ^ polarised Lambek-Grishin calculus
  deriving (Eq,Read,Show)

data SysDescr = SysDescr
  { unaryOp  :: Maybe ConId
  , binaryOp :: ConId
  , downOp   :: Maybe ConId
  , sequent  :: ConId
  , rules    :: [Rule ConId Int]
  , isFinite :: Bool
  }

-- |Parse a string into a logical system.
parseSystem :: String -> System
parseSystem (map toUpper -> "NL" ) = STRNL
parseSystem (map toUpper -> "LG" ) = STRLG
parseSystem (map toUpper -> "CNL") = STRCNL
parseSystem (map toUpper -> "FLG") = POLLG
parseSystem (map toUpper -> sysn ) = read sysn

-- |Return the inference rules associated with a logical system.
getRules :: System -> [Rule ConId Int]
getRules ALGNL   = algNL
getRules ALGNLCL = algNLCL
getRules ALGEXP  = algEXP
getRules STRNL   = strNL
getRules STRCNL  = strCNL
getRules STRLG   = strLG
getRules POLNL   = polNL
getRules POLCNL  = polCNL
getRules POLLG   = polLG


finite :: SysDescr -> SysDescr
finite sysdescr = sysdescr  { isFinite = True }

algebraic :: System -> ConId -> SysDescr
algebraic sys op = SysDescr Nothing op Nothing JForm (getRules sys) False

structural :: System -> ConId -> SysDescr
structural sys op = (algebraic sys op) { downOp = Just Down, sequent = JFocusR  }

withUnary :: ConId -> SysDescr -> SysDescr
withUnary op sysdescr = sysdescr { unaryOp = Just op }


-- |Return the sequent that corresponds to this logical system.
getSysDescr :: System -> SysDescr
getSysDescr ALGNL   = SysDescr Nothing FProd Nothing JForm algNL True
getSysDescr ALGNLCL = SysDescr Nothing FProd Nothing JForm algNLCL False
getSysDescr ALGEXP  = SysDescr (Just FDia) FProd Nothing JForm algEXP True
getSysDescr sys     = SysDescr (Just SDia) SProd (Just Down) JFocusR (getRules sys) True
