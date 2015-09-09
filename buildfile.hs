#!/usr/bin/env runhaskell

{-# LANGUAGE BangPatterns, PatternGuards, OverloadedStrings, RecordWildCards #-}

import           Prelude hiding (exp)
import           Control.Monad (when)
import           Data.Attoparsec.Text (Parser)
import qualified Data.Attoparsec.Text as P
import           Data.Char (isSpace)
import           Data.Either (isLeft)
import qualified Data.List as L
import           Data.List.Split (splitWhen)
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Tuple (swap)
import           Development.Shake hiding ((*>))
import           Development.Shake.FilePath
import           System.IO (hSetEncoding,hGetContents,utf8,IOMode(..),openFile)

srcDir, stdlib, catlib :: FilePath
srcDir = "src"
stdlib = "/Users/pepijn/Projects/agda-stdlib/src"
catlib = "/Users/pepijn/Projects/Categories"

-- TODO:
--
--   * define a filter which checks if all cases in a function are marked as
--     illegal, and marks the type signature as illegal as well if this is the
--     case;
--

--------------------------------------------------------------------------------
-- Mapping: A data structure which holds file mappings
--------------------------------------------------------------------------------

data Mapping =
     Mapping { name           :: String
             , blacklistChar  :: [Text]
             , blacklistToken :: [Text]
             , textMapping    :: [(Text, Text)]
             , include        :: [FilePattern]
             , exclude        :: [FilePattern]
             }

mkMapping :: String -> Mapping
mkMapping name = Mapping
  { name           = name
  , blacklistChar  = []
  , blacklistToken = []
  , textMapping    = []
  , include        = []
  , exclude        = []
  }

--------------------------------------------------------------------------------
-- Makefile
--------------------------------------------------------------------------------

mappings :: [Mapping]
mappings = [nl,nlcps,nlp]


main :: IO ()
main = shakeArgs shakeOptions $ do

  -- Generate: Mappings
  mapM_ make mappings

  -- Generate: Everything.agda
  want [srcDir </> "Everything.agda"]
  srcDir </> "Everything.agda" %> \out -> do

    !modules1 <- fmap (srcDir </>) . filter ("//*.agda"?==) . concat
             <$> mapM makeFileList mappings
    !modules2 <- fmap (srcDir </>) . filter (/="Everything.agda")
             <$> getDirectoryFiles srcDir ["//*.agda","//*.lagda"]
    let modules = L.sort (L.nub (modules1 ++ modules2))

    need ("Header" : modules1)

    !header  <- readFile' "Header"
    !headers <- mapM (liftIO . extractHeader) modules

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




--------------------------------------------------------------------------------
-- Generate: src/Everything.hs
--------------------------------------------------------------------------------

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


---------------------------------------------------------------------------------
-- Make: Non-associative Lambek Calculus
---------------------------------------------------------------------------------

nl :: Mapping
nl = let

  rules01 = ["₀L", "₀R", "⁰L", "⁰R", "r⁰₀", "r₀⁰"
            ,"₁L", "₁R", "¹L", "¹R", "r¹₁", "r₁¹"
            ,"m₀", "m⁰", "m₁", "m¹"]
  check01 = map ("check-" `T.append`) rules01

  in
  (mkMapping "Non-associative Lambek Calculus")
  { blacklistChar  = ["⊕" , "⇛" , "⇚" , "□" , "◇" , "∞" , "[ X ]" , "⟨ X ⟩"
                     ]
  , blacklistToken = ["₀", "₀_", "₀>", "₀>_" , "₀-injective"
                     ,"⁰", "_⁰", "<⁰", "_<⁰" , "⁰-injective"
                     ,"₁", "₁_", "₁>", "₁>_" , "₁-injective"
                     ,"¹", "_¹", "<¹", "_<¹" , "¹-injective"
                     ]
                     ++ rules01
                     ++ check01
  , textMapping    = ["LG" ==> "NL"
                     ]
  , include        = ["Logic/LG.agda"
                     ,"Logic/LG//*.agda"
                     ]
  , exclude        = ["//ToAgda.agda"
                     ,"//LG/Structure.agda"
                     ,"//LG/Structure//*.agda"
                     ,"//LG/ResMon/Origin/Box.agda"
                     ,"//LG/ResMon/Origin/Dia.agda"
                     ,"//LG/ResMon/Origin/Sub*.agda"
                     ,"//LG/ResMon/Origin/Sup0.agda"
                     ,"//LG/ResMon/Origin/Sup1.agda"
                     ,"//LG/ResMon/Origin/Sum.agda"
                     ]
  }


---------------------------------------------------------------------------------
-- Make: NL + CPS
---------------------------------------------------------------------------------

nlcps :: Mapping
nlcps = let

  rules01 = ["₀L", "₀R", "⁰L", "⁰R", "r⁰₀", "r₀⁰"
            ,"₁L", "₁R", "¹L", "¹R", "r¹₁", "r₁¹"
            ,"m₀", "m⁰", "m₁", "m¹"]
  check01 = map ("check-" `T.append`) rules01

  in
  (mkMapping "Syntactically Delimited Lambek Calculus")
  { blacklistChar  = ["⊕" , "⇛" , "⇚" , "□" , "∞" , "[ X ]"
                     ]
  , blacklistToken = ["₀", "₀_", "₀>", "₀>_" , "₀-injective"
                     ,"⁰", "_⁰", "<⁰", "_<⁰" , "⁰-injective"
                     ,"₁", "₁_", "₁>", "₁>_" , "₁-injective"
                     ,"¹", "_¹", "<¹", "_<¹" , "¹-injective"
                     ]
                     ++ rules01
                     ++ check01
  , textMapping    = ["LG" ==> "NLCPS"
                     ]
  , include        = ["Logic/LG.agda"
                     ,"Logic/LG//*.agda"
                     ]
  , exclude        = ["//LG/ToAgda.agda"
                     ,"//LG/Structure.agda"
                     ,"//LG/Structure//*.agda"
                     ,"//LG/EquivalentToResMon.agda"
                     ,"//LG/ResMon/Cut.agda"
                     ,"//LG/ResMon/Origin.agda"
                     ,"//LG/ResMon/Origin/Box.agda"
                     ,"//LG/ResMon/Origin/Sub*.agda"
                     ,"//LG/ResMon/Origin/Sup0.agda"
                     ,"//LG/ResMon/Origin/Sup1.agda"
                     ,"//LG/ResMon/Origin/Sum.agda"
                     ]
  }


---------------------------------------------------------------------------------
-- Make: Non-associative Lambek Calculus
---------------------------------------------------------------------------------

nlp :: Mapping
nlp = let

  rules01 = ["₀L", "₀R", "⁰L", "⁰R", "r⁰₀", "r₀⁰"
            ,"₁L", "₁R", "¹L", "¹R", "r¹₁", "r₁¹"
            ,"m₀", "m⁰", "m₁", "m¹"]
  check01 = map ("check-" `T.append`) rules01

  in
  (mkMapping "Lambek Calculus with Extraction/Infixation")
  { blacklistChar  = ["⊕" , "⇛" , "⇚" , "∞"
                     ]
  , blacklistToken = ["₀", "₀_", "₀>", "₀>_" , "₀-injective"
                     ,"⁰", "_⁰", "<⁰", "_<⁰" , "⁰-injective"
                     ,"₁", "₁_", "₁>", "₁>_" , "₁-injective"
                     ,"¹", "_¹", "<¹", "_<¹" , "¹-injective"
                     ]
                     ++ rules01
                     ++ check01
  , textMapping    = ["LG" ==> "NLP"
                     ]
  , include        = ["Logic/LG.agda"
                     ,"Logic/LG//*.agda"
                     ]
  , exclude        = ["//ToAgda.agda"
                     ,"//LG/ResMon/Base.agda"
                     ,"//LG/ResMon/Origin/*.agda"
                     ]
  }


--------------------------------------------------------------------------------
-- Utility: generate files from other files by restricting the allowed symbols
--          and renaming symbols
--------------------------------------------------------------------------------


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
  action (need . map (srcDir </>) =<< makeFileList m)

  -- define a rule that builds
  patn |%> \out -> do
    let src = apply rev out
    need [src]
    putQuiet $ "Generating " ++ out
    putQuiet $ "      from " ++ src
    liftIO $ do
      !contents <- T.readFile src
      T.writeFile out $
        restrictToFragment src textMapping blacklistToken blacklistChar contents


-- |Parse a file and remove all groups which contain illegal symbols.
restrictToFragment :: FilePath -> [(Text, Text)] -> [Text] -> [Text] -> Text -> Text
restrictToFragment derp replacements blacklistToken blacklistChar input = let

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
  noIllegalTS = filter (all isLegalTypeSignature) groups'

  -- The remaining groups are concatenated back together, now
  -- separated by a single blank line (the reason it has 80 spaces in
  -- there will become apparent soon).
  concatted = L.intercalate [T.append (T.replicate 80 " ") "\n"] noIllegalTS

  -- We mark all illegal lines in two passes, and strip them.
  markIllegal1 = zip (map isLegal concatted) concatted
  markIllegal2 = snd (L.mapAccumL markIllegal (True , 0) markIllegal1)
  stripMarked  = map (T.stripEnd . snd) (filter fst markIllegal2)

  -- We strip the original comment, and then add in a new comment
  -- stating that the file was generated.
  stripComment = dropWhile ("--" `T.isPrefixOf`) stripMarked

  -- We then perform a number of in-place substitutions, which
  -- replace references to the Lambek Grishin calculus with
  -- references to the Lambek calculus.
  replaced = replaceAll (T.unlines stripComment)

  warnComment  = commentBlock `T.append` replaced
  commentBlock = T.unlines [T.replicate 80 "-"
                           ,"-- The Lambek Calculus in Agda"
                           ,"--"
                           ,"-- This file was generated from:"
                           ,"--   " `T.append` T.pack derp
                           ,T.replicate 80 "-"
                           ]

  in warnComment

  where

  -- We then traverse the lines a single time and mark any line
  -- mentioning a blacklisted character.
  --
  -- After that, we traverse the lines a second time. This time with
  -- an accumulating parameter which keeps track of the status of the
  -- previous line. If the previous line was marked as illegal, but
  -- the current line isn't, we check if:
  --
  --   a. the current line is a with statement, in which case it'd be
  --      the continuation of the previous line, or;
  --   b. the current line is more deeply indented than the previous
  --      line, in which case it'd be the direct continuation or in a
  --      where-clause. This case explains the 80 spaces mentioned above.
  --
  -- We then remove all marked lines.
  markIllegal :: (Bool , Int) -> (Bool , Text) -> ((Bool , Int) , (Bool , Text))
  markIllegal (_     , iX) (False , lnY) = ((False , min iX (indent lnY)) , (False , lnY))
  markIllegal (True  , _ ) (True  , lnY) = ((True  ,         indent lnY ) , (True  , lnY))
  markIllegal (False , iX) (True  , lnY) = ((legal , iX) , (legal , lnY))
    where
      legal         = notDeeper && notWithClause
      notDeeper     = iX >= indent lnY
      notWithClause = "..." /= T.take 3 (T.stripStart lnY)

  -- |Check if text contains any blacklisted items.
  isLegal :: Text -> Bool
  isLegal ln = noBlacklistChar && noBlacklistToken
    where
      noBlacklistChar  = not (any (`T.isInfixOf` ln) blacklistChar)
      noBlacklistToken = all (`notElem` tokens) blacklistToken
      tokens           = T.split (`elem` (" (){}" :: String)) ln

  -- |Check if text is a type signature containing blacklisted items.
  isLegalTypeSignature :: Text -> Bool
  isLegalTypeSignature = isLeft . P.parseOnly p
    where
      p :: Parser ()
      p = do
        _ <- P.takeWhile (not . isSpace)
        _ <- P.many1 P.space
        _ <- P.char ':'
        rest <- P.takeText

        when (isLegal rest) $
          fail "Type signature contains no blacklisted items."


  -- |Perform all replacements given in the `replacements` parameter.
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


--------------------------------------------------------------------------------
-- Utility: functions for working with Agda files
--------------------------------------------------------------------------------

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
