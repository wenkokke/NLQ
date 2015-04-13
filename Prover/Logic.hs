{-# LANGUAGE ViewPatterns, FlexibleContexts #-}
module Logic (System(..),parseSystem,getRules,toAgdaFile,tryAll, module X) where


import           Control.Arrow (first)
import           Control.Parallel.Strategies
import           Control.Monad.State
import           Data.Char (toUpper,toLower)
import           Data.List (intersperse)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Void (Void)
import           System.FilePath (takeBaseName)

import           Prover
import           Logic.Base     as X hiding (Term)
import           Logic.DSL      as X
import           Logic.Rules    as X
import           Logic.Printing as X (Agda(..),ASCII(..))
import           Logic.Parsing  as X


-- |Enumeration representing all supported logical systems.
data System
  =  NL |  CNL |  LG
  | FNL | FCNL | FLG
  deriving (Eq,Show)


-- |Return the Agda data type name associated with given a logical
--  system.
toAgdaDataType :: System -> String
toAgdaDataType NL   = "NL"
toAgdaDataType FNL  = "NL"
toAgdaDataType CNL  = "CNL"
toAgdaDataType FCNL = "CNL"
toAgdaDataType LG   = "LG"
toAgdaDataType FLG  = "LG"


-- |Return the Agda module associated with given a logical system.
toAgdaModule :: System -> String
toAgdaModule NL   = error "Error: NL is not yet implemented in Agda."
toAgdaModule FNL  = error "Error: fNL is not yet implemented in Agda."
toAgdaModule CNL  = error "Error: CNL is not yet implemented in Agda."
toAgdaModule FCNL = error "Error: fCNL is not yet implemented in Agda."
toAgdaModule LG   = error "Error: LG is not yet implemented in Agda."
toAgdaModule FLG  = "Example.System.fLG"


-- |Return a valid Agda file given a sequence of proofs.
toAgdaFile :: FilePath
              -> String
              -> System
              -> [(Term ConId Void, [Term String Void])]
              -> Term ConId Void
              -> String
toAgdaFile fn sent sys prfs tgt = unlines (comment ++ [importStmts, "", moduleStmt, ""] ++ proofStmts)
  where
    comment      =
      [ "------------------------------------------------------------------------"
      , "-- The Lambek Calculus in Agda"
      , "------------------------------------------------------------------------"
      , ""
      ]
    moduleStmt   = unlines ["module Example."++takeBaseName fn++" where"]
    importStmts  = unlines ["open import "++toAgdaModule sys]
    dataTypeName = toAgdaDataType sys
    proofStmts   = evalState (concat <$> mapM showProofs prfs) 0
      where
        showProofs (g,ps) = mapM (showProof g) ps
          where
            showProof g p = do
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


-- |Parse a string into a logical system.
parseSystem :: String -> System
parseSystem (map toUpper -> "NL")   = NL
parseSystem (map toUpper -> "CNL")  = CNL
parseSystem (map toUpper -> "LG")   = LG
parseSystem (map toUpper -> "FNL")  = FNL
parseSystem (map toUpper -> "FCNL") = FCNL
parseSystem (map toUpper -> "FLG")  = FLG
parseSystem str = error ("Error: Unknown logical system `"++str++"'.")


-- |Return the inference rules associated with a logical system.
getRules :: System -> [Rule String ConId Int]
getRules NL   = nl
getRules FNL  = fnl
getRules CNL  = cnl
getRules FCNL = fcnl
getRules LG   = lg
getRules FLG  = flg


-- |Create all possible structures from a list of formulas, joining
--  them with the binary structural connective @·⊗·@, and then find
--  all proofs for each of these structures, returning a list of
--  structures paired with their proofs.
--  Note: the resulting list may contain pairs for structures for
--  which no proofs were found.
tryAll :: (NFData r)
          => Map String (Term ConId Void)
          -> [Rule r ConId Int]
          -> String
          -> Term ConId Void
          -> [(Term ConId Void,[Term r Void])]
tryAll lexicon rules sentence y =
  case mapM (`M.lookup` lexicon) (words sentence) of
   Just formulas -> map ((\g -> (g, findAll g rules))
                        .(\x -> Con JFocusR [x,y]))
                    (brackets (·⊗·) formulas)
                    `using` parList rdeepseq
   _             -> []


-- | Generates all binary trees with n nodes. The naive algorithm.
brackets :: (a -> a -> a) -> [a] -> [a]
brackets op = brack where

  brack [ ] = [ ]
  brack [x] = [x]
  brack lst = [l `op` r | (ls,rs) <- split lst, l <- brack ls, r <- brack rs]

  split [_]    = []
  split (x:xs) = ([x],xs) : map (first (x:)) (split xs)
