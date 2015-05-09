{-# LANGUAGE ViewPatterns #-}
module CG.System (System(..),SysInfo(..),desc,descAll,parseSystem,getRules,getSysInfo)where


import Prelude hiding (exp)
import Data.Char (toUpper,toLower)
import Text.Printf (printf)

import CG.Base
import CG.Rules

-- Things that need to be in a '.sys' file
--
-- * name
-- * description
-- * finite (yes/no)
-- * structured (yes/no) (whether or not to use 'down')
-- * structural operators (support for one binary and optionally one unary)
-- * rules


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
  { unaryOp    :: [ConId]
  , binaryOp   :: [ConId]
  , sequent    :: ConId
  , finite     :: Bool
  , structural :: Bool
  , rules      :: [Rule ConId Int]
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


isFinite :: SysInfo -> SysInfo
isFinite sysdescr = sysdescr { finite = True }

algebraic :: System -> SysInfo
algebraic sys = SysInfo [] [FProd] JForm False False (getRules sys)

structured :: System -> SysInfo
structured sys = (algebraic sys) { binaryOp = [SProd], structural = True, sequent = JFocusR  }

withUnary :: ConId -> SysInfo -> SysInfo
withUnary op sysdescr = sysdescr { unaryOp = [op] }


-- |Return the sequent that corresponds to this logical system.
getSysInfo :: System -> SysInfo
getSysInfo ALGNL   = isFinite $ algebraic ALGNL
getSysInfo ALGNLCL =            algebraic ALGNLCL
getSysInfo ALGEXP  = isFinite $ withUnary FDia $ algebraic ALGEXP
getSysInfo sys     = isFinite $ withUnary SDia $ structured sys
