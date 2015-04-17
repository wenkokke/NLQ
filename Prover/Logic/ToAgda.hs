{-# LANGUAGE FlexibleContexts #-}
module Logic.ToAgda (toAgdaFile) where


import Control.Monad.State (State,get,put,evalState)
import Data.Char (toUpper,toLower)
import Data.List (intersperse)
import Data.Void (Void)

import Logic.Base
import Logic.Printing (Agda(..))
import Logic.System (System(..))


-- |Return the Agda data type name associated with given a logical
--  system.
toAgdaDataType :: System -> String
toAgdaDataType    NL   = "NL"
toAgdaDataType    FNL  = "LG"
toAgdaDataType    CNL  = "CNL"
toAgdaDataType    FCNL = "LG"
toAgdaDataType    LG   = "LG"
toAgdaDataType    FLG  = "LG"
toAgdaDataType AlgEXP  = "EXP"
toAgdaDataType AlgNL   = "NL"
toAgdaDataType AlgNLCL = "NLCL"


-- |Return the Agda module associated with given a logical system.
toAgdaModule :: System -> String
toAgdaModule    NL   = error "Error: NL is not yet implemented in Agda."
toAgdaModule    FNL  = "Example.System.fLG"
toAgdaModule    CNL  = error "Error: CNL is not yet implemented in Agda."
toAgdaModule    FCNL = "Example.System.fLG"
toAgdaModule    LG   = error "Error: LG is not yet implemented in Agda."
toAgdaModule    FLG  = "Example.System.fLG"
toAgdaModule AlgEXP  = error "Error: AlgEXP is not yet implemented in Agda."
toAgdaModule AlgNL   = error "Error: AlgNL is not yet implemented in Agda."
toAgdaModule AlgNLCL = "Example.System.NLCL"


-- |Return a valid Agda file given a sequence of proofs.
toAgdaFile :: String
           -> String
           -> System
           -> [(Term Void, Proof)]
           -> Term Void
           -> String
toAgdaFile moduleName sent sys prfs tgt =
  unlines (comment ++ [importStmts, "", moduleStmt, "", proofStmts])
  where
    comment      =
      [ "------------------------------------------------------------------------"
      , "-- The Lambek Calculus in Agda"
      , "------------------------------------------------------------------------"
      , ""
      ]
    moduleStmt   = unlines ["module Example."++moduleName++" where"]
    importStmts  = unlines ["open import "++toAgdaModule sys]
    dataTypeName = toAgdaDataType sys
    proofStmts   = evalState (concat <$> mapM showProof prfs) 0
      where
        showProof (g,p) = do
          n <- get; put (n + 1)
          let subn = sub n
          return $ unlines
            [ synBaseName++subn++" : "++dataTypeName++" "++show (Agda g)
            , synBaseName++subn++" = "++show p
            , semBaseName++subn++" : ⟦ "++show (Agda tgt)++" ⟧ᵀ"
            , semBaseName++subn++" = [ "++synBaseName++subn++" ]ᵀ ("++semCtxt++")"
            ]

    semCtxt = unwords (intersperse "," (words sent ++ ["∅"]))
    semBaseName = map toLower synBaseName
    synBaseName = sanitise sent
      where
        sanitise [] = []
        sanitise (' ':' ': xs) = sanitise (' ':xs)
        sanitise (' '    : xs) = '_' : sanitise xs
        sanitise ('.'    : xs) = sanitise xs
        sanitise (':'    : xs) = sanitise xs
        sanitise ( c     : xs) = toUpper c : sanitise xs


-- |Show a number in subscript.
sub :: Int -> String
sub = map toSub . show
  where
    toSub '0' = '₀'; toSub '5' = '₅'
    toSub '1' = '₁'; toSub '6' = '₆'
    toSub '2' = '₂'; toSub '7' = '₇'
    toSub '3' = '₃'; toSub '8' = '₈'
    toSub '4' = '₄'; toSub '9' = '₉'
