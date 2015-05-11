{-# LANGUAGE RecordWildCards, FlexibleContexts #-}
module CG.ToAgda (Result(..),toAgdaFile) where


import           CG.Base
import           Control.Monad.State (State,get,put,evalState)
import           Data.Char (isSpace,toUpper,toLower)
import           Data.List (intersperse,intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Void (Void)
import           Text.Printf (printf)



toCtxt :: System c -> String -> String
toCtxt sys@System{..} sent
  | structural = unwords (intersperse "," (words sent ++ ["∅"]))
  | otherwise  = unwords (intersperse "," (words sent))

toAgdaName :: System c -> String
toAgdaName System{..} = case agdaName of
  Just n -> n
  _      -> error "Must set agda_name to export to Agda."

toAgdaModule :: System c -> String
toAgdaModule System{..} = case agdaModule of
  Just n -> n
  _      -> error "Must set agda_module to export to Agda."

toBaseName :: Result -> String
toBaseName (Solved     g _) = defaultName g
toBaseName (Parsed s _ _ _) = map toLower (sanitise s)
  where
    sanitise [] = []
    sanitise (' ':' ': xs) = sanitise (' ':xs)
    sanitise (' '    : xs) = '_' : sanitise xs
    sanitise ('.'    : xs) = sanitise xs
    sanitise (':'    : xs) = sanitise xs
    sanitise ( c     : xs) = toUpper c : sanitise xs

defaultName :: (ToString v) => Term ConId v -> String
defaultName = map repl . filter (not . isSpace) . show
  where
    repl '(' = '['
    repl ')' = ']'
    repl  c  =  c

withType :: (ToString v) => Term ConId v -> String -> String
withType = printf "id {A = ⟦ %s ⟧ᵀ} (%s)" . show

agdaList :: [String] -> String
agdaList = unwords . intersperse "\n  ∷" . (++["[]"])

toAgdaDefn :: System c -> Term ConId Void -> Result -> State (Map String Int) String
toAgdaDefn sys goalType ret = case ret of
  (Solved     g p) ->
    return $ unlines
      [ baseName++" : "++dataTypeName++" "++show g
      , baseName++" = "++show p
      , ""
      ]
  (Parsed s e g p) -> do
    n <- next s; let subn = sub n
    return . unlines $
      [ synBaseName++subn++" : "++dataTypeName++" "++show g
      , synBaseName++subn++" \n  = "++show p
      , semBaseName++subn++" : ⟦ "++show goalType++" ⟧ᵀ"
      , semBaseName++subn++" \n  = [ "++synBaseName++subn++" ]ᵀ ("++toCtxt sys s++")"
      , ""
      ]
      ++
      (if null e then [] else
      [ listBaseName++subn++" : List Term"
      , listBaseName++subn++" \n  = "++agdaList (map (\x -> "quoteTerm ("++withType goalType x++")") e)
      , testBaseName++subn++" : Assert (quoteTerm "++semBaseName++subn++" ∈ "++listBaseName++subn++")"
      , testBaseName++subn++" = _"
      , ""
      ])
      ++
      [""]
  where
    baseName     = toBaseName ret
    synBaseName  = map toUpper baseName
    semBaseName  = map toLower baseName
    listBaseName = "LIST_"++baseName
    testBaseName = "TEST_"++baseName
    dataTypeName = toAgdaName sys


-- |Return a valid Agda file given a sequence of proofs.
toAgdaFile :: String -> System c -> [Result] -> Term ConId Void -> String
toAgdaFile moduleName sys prfs goalType =
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
    proofStmts   = evalState (concat <$> mapM (toAgdaDefn sys goalType) prfs) M.empty


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
