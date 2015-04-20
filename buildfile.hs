#!/usr/bin/env runhaskell

{-# LANGUAGE PatternGuards, OverloadedStrings, RecordWildCards #-}

import           Control.Monad (when)
import           Data.Attoparsec.Text (Parser)
import qualified Data.Attoparsec.Text as P
import           Data.Char (isSpace)
import           Data.Either (isRight)
import qualified Data.List as L
import           Data.List.Split (splitWhen)
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Tuple (swap)
import           Development.Shake hiding ((*>))
import           Development.Shake.FilePath
import           System.IO (hSetEncoding,hGetContents,utf8,IOMode(..),openFile)


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

mappings :: [Mapping]
mappings =
  [lambda
  ,linearLambda
  ,nonAssociativeLambek
  ,lambdaCMinus
  ,classicalNonAssociativeLambek
  ,experimentalExtendedLambek
  ]


main :: IO ()
main = shakeArgs shakeOptions $ do

  -- Generate: Mappings
  mapM_ make mappings

  -- Generate: Everything.agda
  want [srcDir </> "Everything.agda"]
  srcDir </> "Everything.agda" %> \out -> do

    modules1 <- fmap (srcDir </>) . filter ("//*.agda"?==) . concat
                <$> mapM makeFileList mappings
    modules2 <- fmap (srcDir </>) . filter (/="Everything.agda")
                <$> getDirectoryFiles srcDir ["//*.agda","//*.lagda"]
    let modules = L.sort (L.nub (modules1 ++ modules2))

    need ("Header" : modules1)

    header  <- readFile' "Header"
    headers <- mapM (liftIO . extractHeader) modules
    writeFile' out $ header ++ format (zip modules headers)

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


  -- Clobber
  "clobber" ~> do
    putNormal "Removing Everything.agda"
    liftIO (removeFiles srcDir ["Everything.agda"])
    mapM_ clobber mappings




-------------------------------------------------------------------------------
-- Generate: src/Everything.hs
-------------------------------------------------------------------------------

extractHeader :: FilePath -> IO [String]
extractHeader file = extract . lines <$> readFileUTF8 file
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
    blacklist   = ["⇛"  , "⇐"  , "□"  , "◇"
                  ," ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀" , "₀>"
                  ,"⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰" , "<⁰"
                  ," ₁" , "{₁" , "(₁" , "r₁¹" , "m₁" , "₁>"
                  ,"¹ " , "¹}" , "¹)" , "r¹₁" , "m¹" , "<¹"
                  ,"⋈"  , "∞"
                  ]
    textMapping = ["Ordered"       ==> "Unrestricted"
                  ,"Structure"     ==> "List Type"
                  ,"LambekGrishin" ==> "LambdaCMinus"
                  ]
    include     = ["Logic/Classical/Ordered/LambekGrishin/Type.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Complexity.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Context.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Context/Polarised.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Polarised.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Subtype.agda"
                  ]
    exclude      = ["//To*.agda"]

--------------------------------------------------------------------------------
-- Make: Non-associative Lambek Calculus
--------------------------------------------------------------------------------

nonAssociativeLambek :: Mapping
nonAssociativeLambek = Mapping{..}
  where
    name        = "Non-associative Lambek Calculus"
    blacklist   = ["⊕"  , "⇛"  , "⇚"  , "□"   , "◇"
                  ," ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀" , "₀>"
                  ,"⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰" , "<⁰"
                  ," ₁" , "{₁" , "(₁" , "r₁¹" , "m₁" , "₁>"
                  ,"¹ " , "¹}" , "¹)" , "r¹₁" , "m¹" , "<¹"
                  ,"⁰ᴸ" , "⁰ᴿ" , "¹ᴸ" , "¹ᴿ"
                  ,"∞"
                  ,"d⇛⇐", "d⇛⇒", "d⇚⇒", "d⇚⇐"
                  ]
    textMapping = ["LambekGrishin" ==> "Lambek"
                  ,"LG"            ==> "NL"
                  ,"Classical"     ==> "Intuitionistic"
                  ]
    include     = ["Logic/Classical/Ordered/LambekGrishin/Type.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type//*.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/ResMon//*.agda"
                  ]
    exclude     = ["//To*.agda"]

--------------------------------------------------------------------------------
-- Make: Non-associative Lambek Calculus
--------------------------------------------------------------------------------

classicalNonAssociativeLambek :: Mapping
classicalNonAssociativeLambek = Mapping{..}
  where
    name        = "Classical Non-associative Lambek Calculus"
    blacklist   = ["d⇛⇐", "d⇛⇒", "d⇚⇒", "d⇚⇐"
                  ]
    textMapping = ["LambekGrishin" ==> "Lambek"
                  ,"LG"            ==> "CNL"
                  ]
    include     = ["Logic/Classical/Ordered/LambekGrishin//*.agda"]
    exclude     = ["//To*.agda"]

--------------------------------------------------------------------------------
-- Make: Experimental Extended Lambek
--------------------------------------------------------------------------------

experimentalExtendedLambek :: Mapping
experimentalExtendedLambek = Mapping{..}
  where
    name        = "Classical Non-associative Lambek Calculus"
    blacklist   = ["d⇛⇐", "d⇛⇒", "d⇚⇒", "d⇚⇐" , "r□◇" , "r◇□"
                  ]
    textMapping = ["LambekGrishin" ==> "Experimental"
                  ,"LG"            ==> "EXP"
                  ]
    include     = ["Logic/Classical/Ordered/LambekGrishin//*.agda"
                  ]
    exclude     = ["//To*.agda"
                  ,"//Trans.agda"
                  ,"//FocPol.agda"
                  ,"//FocPol//*.agda"
                  ,"//EquivalentTo*.agda"
                  ]

--------------------------------------------------------------------------------
-- Make: Unrestricted Lambek-Grishin Calculus
--------------------------------------------------------------------------------
--
--unrestrictedLambekGrishin :: Mapping
--unrestrictedLambekGrishin = Mapping{..}
--  where
--  name        = "Unrestricted Lambek-Grishin Calculus"
--  blacklist   = []
--  textMapping = ["Ordered" ==> "Unrestricted"
--                ]
--  include     = ["Logic/Classical/Ordered/LambekGrishin/Type.agda"
--                ,"Logic/Classical/Ordered/LambekGrishin/Type//*.agda"
--                ,"Logic/Classical/Ordered/LambekGrishin/Structure.agda"
--                ,"Logic/Classical/Ordered/LambekGrishin/Structure//*.agda"
--                ,"Logic/Classical/Ordered/LambekGrishin/Judgement.agda"
--                ]
--  exclude     = ["//To*.agda"]
--
--------------------------------------------------------------------------------
-- Make: Linear Lambek-Grishin Calculus
--------------------------------------------------------------------------------
--
--linearLambekGrishin :: Mapping
--linearLambekGrishin = Mapping{..}
--  where
--  name        = "Linear Lambek-Grishin Calculus"
--  blacklist   = ["⊗ᶜ" , "⊕ᶜ"  , "⊗ʷ" , "⊕ʷ"
--                ]
--  textMapping = ["Unrestricted" ==> "Linear"
--                ]
--  include     = ["Logic/Classical/Unrestricted/LambekGrishin/Base.agda"
--                ,"Logic/Classical/Unrestricted/LambekGrishin/FocPol/Base.agda"
--                ]
--  exclude     = ["//To*.agda"]
--
--------------------------------------------------------------------------------
-- Mapping: Lambda Calculus
--------------------------------------------------------------------------------

lambda :: Mapping
lambda = Mapping{..}
  where
    name        = "Lambda Calculus"
    blacklist   = ["⇐"  , "⊕"  , "⇛"  , "⇚"   , "□"  , "◇"
                  ," ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀" , "₀>"
                  ,"⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰" , "<⁰"
                  ," ₁" , "{₁" , "(₁" , "r₁¹" , "m₁" , "₁>"
                  ,"¹ " , "¹}" , "¹)" , "r¹₁" , "m¹" , "<¹"
                  ,"⋈"  , "∞"
                  ]
    textMapping = [ "LG"            ==> "Λ"
                  , "Classical"     ==> "Intuitionistic"
                  , "Ordered"       ==> "Unrestricted"
                  , "LambekGrishin" ==> "Lambda"
                  ]
    include     = ["Logic/Classical/Ordered/LambekGrishin/Type.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Complexity.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Context.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Context/Polarised.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Polarised.agda"
                  ,"Logic/Classical/Ordered/LambekGrishin/Type/Subtype.agda"
                  ]
    exclude     = ["//To*.agda"]

--------------------------------------------------------------------------------
-- Mapping: Linear Lambda Calculus
--------------------------------------------------------------------------------

linearLambda :: Mapping
linearLambda = Mapping{..}
  where
    name        = "Linear Lambda Calculus"
    blacklist   = ["wᴸ₁" , "wᴸ" , "cᴸ₁" , "cᴸ"
                  ]
    textMapping = ["Unrestricted" ==> "Linear"
                  ]
    include     = ["Logic/Intuitionistic/Unrestricted/Lambda/Base.agda"
                  ,"Logic/Intuitionistic/Unrestricted/Lambda/Permute.agda"
                  ]
    exclude     = ["//To*.agda"]

-------------------------------------------------------------------------------
-- Utility: generate files from other files by restricting the allowed symbols
--          and renaming symbols
-------------------------------------------------------------------------------


clobber :: Mapping -> Action ()
clobber m@Mapping{..} = do
  putNormal $ "Removing generated files for " ++ name
  fileList <- makeFileList m
  liftIO (removeFiles srcDir fileList)


apply :: [(Text, Text)] -> FilePath -> FilePath
apply [] = id
apply mapping = T.unpack . go mapping . T.pack
  where
    go [] = id
    go ((from,to):rest) = T.replace from to . go rest


makeFileList :: Mapping -> Action [FilePath]
makeFileList Mapping{..} = do
  included <- getDirectoryFiles srcDir include
  let excluded = filter (\src -> not (any (?== src) exclude)) included
  let mapped   = apply textMapping <$> excluded
  return mapped


make :: Mapping -> Rules ()
make m@Mapping{..} = do

  -- compute the destination pattern
  let patn = fmap ((srcDir </>) . apply textMapping) include
  let rev  = map swap textMapping

  -- require files
  action (need . (map (srcDir </>)) =<< makeFileList m)

  -- define a rule that builds
  patn |%> \out -> do

    let src = apply rev out

    need [src]

    putQuiet $ "Generating " ++ out

    liftIO $
      T.writeFile out . restrictSource textMapping blacklist =<< T.readFile src


-- |Parse a file and remove all groups which contain illegal symbols.
restrictSource :: [(Text, Text)] -> [Text] -> Text -> Text
restrictSource replacements blacklist input = let

  -- The algorithm to remove illegal lines is as follows:
  -- First we divide the text up by lines, and group the lines that
  -- are separated by one or more blank lines.
  inputLines = T.lines input
  groups     = splitWhen isBlank inputLines
  groups'    = map (filter (not . isBlank)) groups

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

  -- Add in a comment stating that the file was generated.
  comment      = "-- This file was automatically generated." :: Text
  withComment  = case stripEnd of
    (x:y:rest) -> x:y:comment:rest

  -- We then perform a number of in-place substitutions, which
  -- replace references to the Lambek Grishin calculus with
  -- references to the Lambek calculus.
  replaced = replaceAll (T.unlines withComment)

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
