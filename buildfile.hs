#!/usr/bin/env runhaskell

{-# LANGUAGE PatternGuards, OverloadedStrings, RecordWildCards #-}

import           Control.Applicative ((<$>))
import           Control.Monad (when)
import           Data.Attoparsec.Text (Parser)
import qualified Data.Attoparsec.Text as P
import           Data.Char (isSpace)
import           Data.Either (isRight)
import qualified Data.List as L
import           Data.List.Split (splitWhen)
import qualified Data.Maybe as M
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Tuple (swap)
import           Development.Shake hiding ((*>))
import           Development.Shake.FilePath
import           System.IO (hPutStr,hSetEncoding,hGetContents,utf8,IOMode(..),openFile,withFile)


srcDir, stdlib, catlib, prover :: FilePath
srcDir = "src"
stdlib = "/Users/pepijn/Projects/agda-stdlib/src"
catlib = "/Users/pepijn/Projects/Categories"
prover = "prover"


-------------------------------------------------------------------------------
-- Mapping: A data structure which holds file mappings
-------------------------------------------------------------------------------

data Mapping =
     Mapping { name        :: String
             , blacklist   :: [Text]
             , textMapping :: [(Text, Text)]
             , include     :: [FilePattern]
             , exclude     :: [FilePattern]
             }

-------------------------------------------------------------------------------
-- Makefile
-------------------------------------------------------------------------------

main :: IO ()
main = shakeArgs shakeOptions $ do


  make lambda
  make linearLambda
  make nonAssociativeLambek

  make lambdaCMinus
  make linearLambekGrishin
  make classicalNonAssociativeLambek


  -- Generate: Everything
  want [srcDir </> "Everything.agda"]
  srcDir </> "Everything.agda" %> \out -> do

    liftIO (removeFiles srcDir ["Everything.agda"])

    modules <- L.sort . fmap (srcDir </>) . filter (not . (=="Everything.agda"))
            <$> getDirectoryFiles srcDir ["//*.agda","//*.lagda"]
    need ("Header" : modules)
    header  <- readFile' "Header"
    headers <- mapM (liftIO . extractHeader) modules
    writeFile' out $
      header ++ format (zip modules headers)

  -- Generate: Listings
  phony "listings" $ do
    need [srcDir </> "Everything.agda"]
    cmd ("agda" :: String)
        ["--include-path=" ++ srcDir
        ,"--include-path=" ++ stdlib
        ,"--include-path=" ++ catlib
        ,"--html"
        ,"src/Everything.agda"
        ,"-v0"]

  -- Clobber: Clean up after various tasks
  "clobber" ~> do

    putNormal "Removing Everything.agda"
    liftIO $ removeFiles srcDir ["Everything.agda"]


    clobber lambda
    clobber linearLambda
    clobber nonAssociativeLambek

    clobber lambdaCMinus
    clobber linearLambekGrishin
    clobber classicalNonAssociativeLambek

    putNormal "Removing generated prover files"
    liftIO $ removeFiles prover
      [ "proof.agda" , "proof.aux" , "proof.log" , "proof.out"
      , "proof.pdf"  , "proof.pl"  , "proof.tex" , "prover"
      ]



-------------------------------------------------------------------------------
-- Generate: src/Everything.hs
-------------------------------------------------------------------------------

extractHeader :: FilePath -> IO [String]
extractHeader file = fmap (extract . lines) $ readFileUTF8 file
  where
    isDelimiter = all (== '-')
    strip       = reverse. dropWhile isDelimiter . reverse . dropWhile isDelimiter

    extract (d1 : "-- The Lambek Calculus in Agda" : ss)
      | isDelimiter d1
      , (info, d2 : _) <- span ((==2) . length . takeWhile (=='-')) ss
      , isDelimiter d2
      = strip info
    extract _ = error $ file ++ " is malformed."


-- | Formats the extracted module information.
format :: [(FilePath, [String])] -> String
format = unlines . concatMap fmt
  where
    fmt (file, header) = sep : header ++ ["import " ++ fileToMod file]
      where
        sep | '.' `elem` file = ""
            | otherwise       = "\n"



--------------------------------------------------------------------------------
-- Make: Lambda C-Minus
--------------------------------------------------------------------------------

lambdaCMinus :: Mapping
lambdaCMinus = Mapping{..}
  where
    name        = "Lambda C-Minus Calculus"
    blacklist   = [ "⇛"  , "⇐"  , "□"  , "◇"
                  , " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹"
                  ]
    textMapping = [ "Ordered"       ==> "Unrestricted"
                  , "Structure"     ==> "List Type"
                  , "LambekGrishin" ==> "LambdaCMinus"
                  ]
    include     = [ srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Complexity.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Context.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Context/Polarised.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Polarised.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Subtype.agda"
                  ]
    exclude      = []

--------------------------------------------------------------------------------
-- Make: Non-associative Lambek Calculus
--------------------------------------------------------------------------------

nonAssociativeLambek :: Mapping
nonAssociativeLambek = Mapping{..}
  where
    name        = "Non-associative Lambek Calculus"
    blacklist   = [ "⊕"  , "⇛"  , "⇚"  , "□"   , "◇"
                  , " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹"
                  , "⁰ᴸ" , "⁰ᴿ" , "¹ᴸ" , "¹ᴿ"
                  ]
    textMapping = [ "LambekGrishin" ==> "Lambek"
                  , "LG"            ==> "NL"
                  , "Classical"     ==> "Intuitionistic"
                  ]
    include     = [srcDir </> "Logic/Classical/Ordered/LambekGrishin//*.agda"]
    exclude     = ["//ToIntuitionisticLinearLambda.agda"]

--------------------------------------------------------------------------------
-- Make: Non-associative Lambek Calculus
--------------------------------------------------------------------------------

classicalNonAssociativeLambek :: Mapping
classicalNonAssociativeLambek = Mapping{..}
  where
    name        = "Classical Non-associative Lambek Calculus"
    blacklist   = [ "d⇛⇐", "d⇛⇒", "d⇚⇒", "d⇚⇐" ]
    textMapping = [ "LambekGrishin" ==> "Lambek"
                  , "LG"            ==> "CNL"    ]
    include     = [srcDir </> "Logic/Classical/Ordered/LambekGrishin//*.agda"]
    exclude     = []




--------------------------------------------------------------------------------
-- Make: Linear Lambek-Grishin Calculus
--------------------------------------------------------------------------------


linearLambekGrishin :: Mapping
linearLambekGrishin = Mapping{..}
  where
  name        = "Linear Lambek-Grishin Calculus"
  blacklist   = [ "⊗ᶜ" , "⊕ᶜ"  , "⊗ʷ" , "⊕ʷ" ]
  textMapping = [ "Unrestricted" ==> "Linear" ]
  include     = [ srcDir </> "Logic/Classical/Unrestricted/LambekGrishin/Base.agda"
                , srcDir </> "Logic/Classical/Unrestricted/LambekGrishin/FocPol/Base.agda"
                ]
  exclude     = []


--------------------------------------------------------------------------------
-- Mapping: Lambda Calculus
--------------------------------------------------------------------------------


lambda :: Mapping
lambda = Mapping{..}
  where
    name        = "Lambda Calculus"
    blacklist   = [ "⇐"  , "⊕"  , "⇛"  , "⇚"   , "□"  , "◇"
                  , " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹"
                  ]
    textMapping = [ "LG"            ==> "Λ"
                  , "Classical"     ==> "Intuitionistic"
                  , "Ordered"       ==> "Unrestricted"
                  , "LambekGrishin" ==> "Lambda"
                  ]
    include     = [ srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Complexity.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Context.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Context/Polarised.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Polarised.agda"
                  , srcDir </> "Logic/Classical/Ordered/LambekGrishin/Type/Subtype.agda"
                  ]
    exclude     = []

--------------------------------------------------------------------------------
-- Mapping: Linear Lambda Calculus
--------------------------------------------------------------------------------

linearLambda :: Mapping
linearLambda = Mapping{..}
  where
    name        = "Linear Lambda Calculus"
    blacklist   = [ "wᴸ₁" , "wᴸ" , "cᴸ₁" , "cᴸ" ]
    textMapping = [ "Unrestricted" ==> "Linear"
                  ]
    include     = [ srcDir </> "Logic/Intuitionistic/Unrestricted/Lambda/Base.agda"
                  , srcDir </> "Logic/Intuitionistic/Unrestricted/Lambda/Permute.agda"
                  ]
    exclude     = []


-------------------------------------------------------------------------------
-- Utility: generate files from other files by restricting the allowed symbols
--          and renaming symbols
-------------------------------------------------------------------------------


clobber :: Mapping -> Action ()
clobber Mapping{..} = do
  putNormal $ "Removing generated files for " ++ name
  liftIO . removeFiles "." =<< map (apply textMapping) <$> getDirectoryFiles "." include


apply :: [(Text, Text)] -> FilePath -> FilePath
apply [] = id
apply mapping = T.unpack . go mapping . T.pack
  where
    go [] = id
    go ((from,to):rest) = T.replace from to . go rest


make :: Mapping -> Rules ()
make Mapping{..} = do

  -- compute the destination pattern
  let dstPattern = apply textMapping <$> include
  let revMapping = map swap textMapping

  -- require all files that match any of the file patterns
  action $ need =<< map (apply textMapping)
                <$> filter (\src -> not (any (?== src) exclude))
                <$> getDirectoryFiles "." include

  -- define a rule that builds
  dstPattern |%> \dst -> do

    let src = apply revMapping dst

    need [src]

    putQuiet $ "Generating " ++ dst

    liftIO $
      T.writeFile dst . restrictSource textMapping blacklist =<< T.readFile src


-- |Parse a file and remove all groups which contain illegal symbols.
restrictSource :: [(Text, Text)] -> [Text] -> Text -> Text
restrictSource replacements blacklist input = let

  -- The algorithm to remove illegal lines is as follows:
  -- First we divide the text up by lines, and group the lines that
  -- are separated by one or more blank lines.
  lines   = T.lines input
  groups  = splitWhen isBlank lines
  groups' = map (filter (not . isBlank)) groups

  -- Then we scan over all the groups, and remove those which have a
  -- type signature which mentions one of the blacklisted characters.
  -- The idea here is to remove functions that implement an illegal
  -- type signature.
  noIllegalTS = filter (all (not . isIllegalTS)) groups'

  -- The remaining groups are concatenated back together, now
  -- separated by a single blank line (the reason it has 80 spaces in
  -- there will become apparent soon).
  concatted = L.intercalate [T.append (T.replicate 80 " ") "\n"] noIllegalTS

  -- We then traverse the lines a single time and mark any line
  -- mentioning a blacklisted character.
  --
  -- After that, we traverse the lines a second time. This time with
  -- an accumulating parameter which keeps track of the status of the
  -- previous line. If the previous line was marked as illegal, but
  -- the current line isn't, we check if:
  --   a. the current line is a with statement, in which case it'd be
  --      the continuation of the previous line, or;
  --   b. the current line is more deeply indented than the previous
  --      line, in which case it'd be the direct continuation or in a
  --      where-clause. This case explains the 80 spaces mentioned above.
  --
  -- We then remove all marked lines.
  markIllegal  = zip (map isLegal concatted) concatted
  markIllegal' :: [(Bool, Text)]
  markIllegal' = snd (L.mapAccumL go (True , 0) markIllegal)
    where go :: (Bool , Int) -> (Bool , Text) -> ((Bool , Int) , (Bool , Text))
          go (_     , iX) (False , lnY) = ((False , min iX (indent lnY)) , (False , lnY))
          go (True  , _ ) (True  , lnY) = ((True  ,         indent lnY ) , (True  , lnY))
          go (False , iX) (True  , lnY) = ((legal , iX) , (legal , lnY))
            where
              legal         = notDeeper && notWithClause
              notDeeper     = iX >= indent lnY
              notWithClause = "..." /= T.take 3 (T.stripStart lnY)
  stripMarked  = map snd (filter fst markIllegal')
  stripEnd     = map T.stripEnd stripMarked

  -- We then perform a number of in-place substitutions, which
  -- replace references to the Lambek Grishin calculus with
  -- references to the Lambek calculus.
  replaced = replaceAll (T.unlines stripEnd)

  in replaced

  where

  -- |Check if text contains any blacklisted items.
  isLegal :: Text -> Bool
  isLegal  = not . foldr (\x f y -> f y || x `T.isInfixOf` y) (const False) blacklist

  -- |Check if text is a type signature containing blacklisted items.
  isIllegalTS :: Text -> Bool
  isIllegalTS = isRight . P.parseOnly p
    where
      p :: Parser ()
      p = do
        _ <- P.takeWhile (not . isSpace)
        _ <- P.many1 P.space
        _ <- P.char ':'
        rest <- P.takeText

        when (isLegal rest) $
          fail "Type signature contains no blacklisted items."


  -- |Perform all replacements given in the `replacements` paramter.
  replaceAll :: Text -> Text
  replaceAll = foldr (\(x,y) f -> f . T.replace x y) id replacements

  -- |Get the indentation for a line.
  indent :: Text -> Int
  indent = T.length . T.takeWhile isSpace

  -- |Check if a text is completely blank.
  isBlank :: Text -> Bool
  isBlank = T.all isSpace


infix 4 ==>

(==>) :: a -> b -> (a , b)
(==>) = (,)


-------------------------------------------------------------------------------
-- Utility: functions for working with Agda files
-------------------------------------------------------------------------------

-- | Translates a file name to the corresponding module name. It is
-- assumed that the file name corresponds to an Agda module under
-- 'srcDir'.
fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c

-- | A variant of 'readFile' which uses the 'utf8' encoding.
readFileUTF8 :: FilePath -> IO String
readFileUTF8 f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  hGetContents h

-- | A variant of 'writeFile' which uses the 'utf8' encoding.
writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s
