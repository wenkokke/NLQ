{-# LANGUAGE FlexibleContexts #-}
module Logic.ToAgda (Result(..),toAgdaFile) where


import           Control.Monad.State (State,get,put,evalState)
import           Data.Char (isSpace,toUpper,toLower)
import           Data.List (intersperse,intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Void (Void)
import           Text.Printf (printf)

import           Logic.Base
import           Logic.Printing (Agda(..))
import           Logic.System (System(..))


data Result
  = Solved                 (Term Void) Proof
  | Parsed String [String] (Term Void) Proof


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

getBaseName :: Result -> String
getBaseName (Solved     g _) = defaultName g
getBaseName (Parsed s _ _ _) = map toLower (sanitise s)
  where
    sanitise [] = []
    sanitise (' ':' ': xs) = sanitise (' ':xs)
    sanitise (' '    : xs) = '_' : sanitise xs
    sanitise ('.'    : xs) = sanitise xs
    sanitise (':'    : xs) = sanitise xs
    sanitise ( c     : xs) = toUpper c : sanitise xs

defaultName :: Term Void -> String
defaultName = map repl . filter (not . isSpace) . show . Agda
  where
    repl '(' = '['
    repl ')' = ']'
    repl  c  =  c

withType :: Term Void -> String -> String
withType = printf "id {A = ⟦ %s ⟧ᵀ} (%s)" . show . Agda

agdaList :: [String] -> String
agdaList = unwords . intersperse "\n  ∷" . (++["[]"])

toAgdaDefn :: System -> Term Void -> Result -> State (Map String Int) String
toAgdaDefn sys tgt ret = case ret of
  (Solved     g p) ->
    return $ unlines
      [ baseName++" : "++dataTypeName++" "++show (Agda g)
      , baseName++" = "++show p
      , ""
      ]
  (Parsed s e g p) -> do
    n <- next s; let subn = sub n
    return . unlines $
      [ synBaseName++subn++" : "++dataTypeName++" "++show (Agda g)
      , synBaseName++subn++" \n  = "++show p
      , semBaseName++subn++" : ⟦ "++show (Agda tgt)++" ⟧ᵀ"
      , semBaseName++subn++" \n  = [ "++synBaseName++subn++" ]ᵀ ("++toCtxt sys s++")"
      , ""
      ]
      ++
      (if null e then [] else
      [ listBaseName++subn++" : List Term"
      , listBaseName++subn++" \n  = "++agdaList (map (\x -> "quoteTerm ("++withType tgt x++")") e)
      , testBaseName++subn++" : Assert (quoteTerm "++semBaseName++subn++" ∈ "++listBaseName++subn++")"
      , testBaseName++subn++" = _"
      , ""
      ])
      ++
      [""]
  where
    baseName     = getBaseName ret
    synBaseName  = map toUpper baseName
    semBaseName  = map toLower baseName
    listBaseName = "LIST_"++baseName
    testBaseName = "TEST_"++baseName
    dataTypeName = toAgdaDataType sys


-- |Return a valid Agda file given a sequence of proofs.
toAgdaFile :: String -> System -> [Result] -> Term Void -> String
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
    importStmts  = unlines
      [ "open import Data.Bool using (Bool; true; false; _∧_; _∨_)"
      , "open import Data.List using (List; _∷_; [])"
      , "open import Function using (id)"
      , "open import Reflection using (Term)"
      , "open import "++toAgdaModule sys
      ]
    proofStmts   = evalState (concat <$> mapM (toAgdaDefn sys tgt) prfs) M.empty


-- |Compute the next number for this String.
next :: String -> State (Map String Int) Int
next s = do m <- get
            let n = fromMaybe 0 (M.lookup s m)
            put (M.insert s (n + 1) m)
            return n


-- |Show a number in subscript.
sub :: Int -> String
sub = map toSub . show
  where
    toSub '0' = '₀'; toSub '5' = '₅'
    toSub '1' = '₁'; toSub '6' = '₆'
    toSub '2' = '₂'; toSub '7' = '₇'
    toSub '3' = '₃'; toSub '8' = '₈'
    toSub '4' = '₄'; toSub '9' = '₉'
