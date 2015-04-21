{-# LANGUAGE FlexibleContexts #-}
module Logic.ToAgda (toAgdaFile) where


import           Control.Monad.State (State,get,put,evalState)
import           Data.Char (toUpper,toLower)
import           Data.List (intersperse)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Void (Void)

import           Logic.Base
import           Logic.Printing (Agda(..))
import           Logic.System (System(..))


-- |Return the Agda data type name associated with given a logical
--  system.
toAgdaDataType :: System -> String
toAgdaDataType ALGEXP  = "EXP"
toAgdaDataType ALGNL   = "NL"
toAgdaDataType ALGNLCL = "NL"
toAgdaDataType STRNL   = "NL"
toAgdaDataType STRCNL  = "CNL"
toAgdaDataType STRLG   = "LG"
toAgdaDataType POLNL   = "LG"
toAgdaDataType POLCNL  = "LG"
toAgdaDataType POLLG   = "LG"


-- |Return the Agda module associated with given a logical system.
toAgdaModule :: System -> String
toAgdaModule ALGEXP  = error "Error: AlgEXP is not yet implemented in Agda."
toAgdaModule ALGNL   = error "Error: AlgNL is not yet implemented in Agda."
toAgdaModule ALGNLCL = "Example.System.NLCL"
toAgdaModule STRNL   = error "Error: NL is not yet implemented in Agda."
toAgdaModule STRCNL  = error "Error: CNL is not yet implemented in Agda."
toAgdaModule STRLG   = error "Error: LG is not yet implemented in Agda."
toAgdaModule POLNL   = "Example.System.fLG"
toAgdaModule POLCNL  = "Example.System.fLG"
toAgdaModule POLLG   = "Example.System.fLG"


toCtxt :: System -> String -> String
toCtxt sys sent = case sys of
  ALGNL   -> useProd
  ALGNLCL -> useProd
  ALGEXP  -> useProd
  _       -> useEnv
  where
    useEnv  = unwords (intersperse "," (words sent ++ ["∅"]))
    useProd = unwords (intersperse "," (words sent))


next :: String -> State (Map String Int) Int
next s = do m <- get
            let n = fromMaybe 0 (M.lookup s m)
            put (M.insert s (n + 1) m)
            return n

-- |Return a valid Agda file given a sequence of proofs.
toAgdaFile :: String
           -> System
           -> [(String, (Term Void, Proof))]
           -> Term Void
           -> String
toAgdaFile moduleName sys prfs tgt =
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
    proofStmts   = evalState (concat <$> mapM showProof prfs) M.empty
      where
        showProof (sent,(g,p)) = do
          n <- next sent
          let subn = sub n
          return $ unlines
            [ synBaseName++subn++" : "++dataTypeName++" "++show (Agda g)
            , synBaseName++subn++" = "++show p
            , semBaseName++subn++" : ⟦ "++show (Agda tgt)++" ⟧ᵀ"
            , semBaseName++subn++" = [ "++synBaseName++subn++" ]ᵀ ("++semCtxt++")"
            , ""
            ]
          where
            semCtxt     = toCtxt sys sent
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
