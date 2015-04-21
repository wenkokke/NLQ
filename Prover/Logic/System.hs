{-# LANGUAGE ViewPatterns #-}
module Logic.System (System(..),SysInfo(..),desc,descAll,parseSystem,getRules,getSysInfo)where


import Prelude hiding (exp)
import Data.Char (toUpper,toLower)
import Text.Printf (printf)

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
  deriving (Eq,Read,Show,Enum,Bounded)


desc :: System -> String
desc ALGNL   = "Algebraic non-associative Lambek calculus."
desc ALGNLCL = "Algebraic Lambek calculus (by Barker & Shan)."
desc ALGEXP  = "Algebraic experimental Lambek calculus (with 'reset')."
desc STRNL   = "Structured non-associative Lambek calculus."
desc STRCNL  = "Structured classical non-associative Lambek calculus."
desc STRLG   = "Structured Lambek-Grishin."
desc POLNL   = "Polarised non-associative Lambek calculus (extracted from polarised LG)."
desc POLCNL  = "Polarised classical non-associative Lambek calculus (extracted from polarised LG)."
desc POLLG   = "Polarised Lambek-Grishin calculus."


descAll :: String
descAll = unlines ("":"Available Systems":"": map descLine [minBound..maxBound])
  where
    descLine sys = printf "  %-17s%s" (map toLower $ show sys) (desc sys)


data SysInfo = SysInfo
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


finite :: SysInfo -> SysInfo
finite sysdescr = sysdescr  { isFinite = True }

algebraic :: System -> ConId -> SysInfo
algebraic sys op = SysInfo Nothing op Nothing JForm (getRules sys) False

structural :: System -> ConId -> SysInfo
structural sys op = (algebraic sys op) { downOp = Just Down, sequent = JFocusR  }

withUnary :: ConId -> SysInfo -> SysInfo
withUnary op sysdescr = sysdescr { unaryOp = Just op }


-- |Return the sequent that corresponds to this logical system.
getSysInfo :: System -> SysInfo
getSysInfo ALGNL   = SysInfo Nothing FProd Nothing JForm algNL True
getSysInfo ALGNLCL = SysInfo Nothing FProd Nothing JForm algNLCL False
getSysInfo ALGEXP  = SysInfo (Just FDia) FProd Nothing JForm algEXP True
getSysInfo sys     = SysInfo (Just SDia) SProd (Just Down) JFocusR (getRules sys) True
