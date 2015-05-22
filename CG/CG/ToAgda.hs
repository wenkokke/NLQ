{-# LANGUAGE RecordWildCards, FlexibleContexts #-}
module CG.ToAgda (Result(..),writeAgdaFile) where


import           CG.Base
import           Control.Monad.State (State,get,put,runState)
import           Data.Char (isSpace,toUpper,toLower)
import           Data.List (intersperse,intercalate)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe)
import           Data.Void (Void)
import           System.IO
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

sanitise [] = []
sanitise (' ':' ': xs) = sanitise (' ':xs)
sanitise (' '    : xs) = '_' : sanitise xs
sanitise ('.'    : xs) = sanitise xs
sanitise (':'    : xs) = sanitise xs
sanitise ( c     : xs) = toUpper c : sanitise xs

sanitiseForLaTeX [] = []
sanitiseForLaTeX ('_':xs) = '\\' : '_' : sanitiseForLaTeX xs
sanitiseForLaTeX ( c :xs) =         c  : sanitiseForLaTeX xs

defaultName :: (Show v, ToString v) => Term ConId v -> String
defaultName = map repl . filter (not . isSpace) . show
  where
    repl '(' = '['
    repl ')' = ']'
    repl  c  =  c

withType :: (Show v, ToString v) => Term ConId v -> String -> String
withType = printf "id {A = ⟦ %s ⟧ᵀ} (%s)" . show

agdaList :: [String] -> String
agdaList = unwords . intersperse "\n  ∷" . (++["[]"])

agdaList' :: [String] -> String
agdaList' = unwords . intersperse " ∷" . (++["[]"])

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
writeAgdaFile :: Handle -> String -> System c -> [Result] -> Term ConId Void -> IO [String]
writeAgdaFile h moduleName sys@System{..} prfs goalType = do

  let (proofDefn, nameMap) =
        runState (mapM (toAgdaDefn sys goalType) prfs) M.empty
  let nameList = toNameList nameMap
  let fileList = map (\(i,s) -> map toLower (sanitise s) ++ "_" ++ show i) nameList

  mapM_ (hPutStrLn h) $
    [ "------------------------------------------------------------------------"
    , "-- The Lambek Calculus in Agda"
    , "------------------------------------------------------------------------"
    , ""
    , "open import Data.Colist using (fromList)"
    , "open import Data.Bool   using (Bool; true; false; _∧_; _∨_)"
    , "open import Data.List   using (List; _∷_; [])"
    , "open import Data.String using (String)"
    , "open import Data.Vec    using (_∷_; [])"
    , "open import Function    using (id)"
    , "open import IO          using (IO; mapM′; run)"
    , "open import Reflection  using (Term)"
    , "open import "++toAgdaModule sys
    , ""
    , "module "++moduleName++" where"
    , ""
    , unlines proofDefn
    , ""
    , "proofList : List Proof"
    , "proofList\n  = " ++ (agdaList (proofList structural nameList))
    , ""
    , "main : _"
    , "main = run (mapM′ writeProof (fromList proofList))"
    ]

  return fileList


-- |Convert a given map of sentences to max IDs, to a list of names.
toNameList :: Map String Int -> [(Int, String)]
toNameList sentenceIds =
  [(j,s) | (s,i) <- M.toList sentenceIds, j <- [0..i-1]]


-- |Return a single list which contains all proofs as LaTeX strings.
proofList :: Bool -> [(Int, String)] -> [String]
proofList structural nameList = do
  (i,s) <- nameList
  let
    fileName = map toLower (sanitise s) ++ "_" ++ show i
    termName = map toUpper (sanitise s) ++ sub i
    sentence = sanitiseForLaTeX (toUpper (head s) : map toLower (tail s) ++ ".")
    wordList = if structural
               then agdaList' (map (show . sanitiseForLaTeX) (words s))
               else agdaList' [show (sanitiseForLaTeX (sanitise s))]
  return $
    printf "proof %s %s (toLaTeX %s) (toLaTeXTerm (%s) (toTerm %s))"
    (show fileName) (show sentence) termName wordList termName


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
