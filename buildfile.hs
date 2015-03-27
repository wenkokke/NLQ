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
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Tuple (swap)
import           Development.Shake
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
     Mapping { blacklist   :: [Text]
             , textMapping :: [(Text, Text)]
             , fileMapping :: [(FilePath, FilePath)]
             }

-------------------------------------------------------------------------------
-- Makefile
-------------------------------------------------------------------------------

main :: IO ()
main = shakeArgs shakeOptions $ do


  run makeLambda
  run makeLinearLambda
  run makeLambek
  run makeLambdaCMinus
  run makeLinearLambekGrishin
  run makeUnrestrictedLambekGrishin


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
  phony "clobber" $ do
    putNormal "Removing Everything.agda"
    liftIO $ removeFiles srcDir ["Everything.agda"]

    putNormal "Removing generated files for Lambda Calculus"
    clobber makeLambda
    putNormal "Removing generated files for Linear Lambda Calculus"
    clobber makeLinearLambda
    putNormal "Removing generated files for Lambek Calculus"
    clobber makeLambek
    putNormal "Removing generated files for Lambek C-Minus Calculus"
    clobber makeLambdaCMinus
    putNormal "Removing generated files for Linear Lambek Grishin"
    clobber makeLinearLambekGrishin
    putNormal "Removing generated files for Unrestricted Lambek Grishin"
    clobber makeUnrestrictedLambekGrishin

    putNormal "Removing generated prover files"
    liftIO $ removeFiles prover [ "proof.agda" , "proof.aux" , "proof.log" , "proof.out"
                                , "proof.pdf"  , "proof.pl"  , "proof.tex" , "prover"]



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


makeLambdaCMinus :: Mapping
makeLambdaCMinus  = Mapping
  { blacklist   = [ "⇛"  , "⇐"  , "□"  , "◇"
                  , " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹"
                  ]
  , textMapping = [ "Ordered"       ==> "Unrestricted"
                  , "Structure"     ==> "List Type"
                  , "LambekGrishin" ==> "LambdaCMinus"
                  ]
  , fileMapping = [ srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambdaCMinus"  </> "Type.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambdaCMinus"  </> "Type" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Context.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambdaCMinus"  </> "Type" </> "Context.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Context" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambdaCMinus"  </> "Type" </> "Context" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambdaCMinus"  </> "Type" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Subtype.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambdaCMinus"  </> "Type" </> "Subtype.agda"
                  ]
  }


--------------------------------------------------------------------------------
-- Make: Lambek Calculus
--------------------------------------------------------------------------------

makeLambek :: Mapping
makeLambek  = Mapping
  { blacklist   = [ "⊕"  , "⇛"  , "⇚"  , "□"   , "◇"
                  , " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹"
                  , "⁰ᴸ" , "⁰ᴿ" , "¹ᴸ" , "¹ᴿ"
                  ]
  , textMapping = [ "LambekGrishin" ==> "Lambek"
                  , "LG"            ==> "NL"
                  , "Classical"     ==> "Intuitionistic"
                  ]
  , fileMapping = [ srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Type.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Type.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Type" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Type" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Type" </> "Context.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Type" </> "Context.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Type" </> "Context" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Type" </> "Context" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Type" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Type" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Type" </> "Subtype.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Type" </> "Subtype.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Structure.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Structure.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Structure" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Structure" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Structure" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Structure" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Judgement.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Judgement.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Base.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Base.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "Normal" </> "Base.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "Normal" </> "Base.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon" </> "Judgement.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon" </> "Judgement.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon" </> "Judgement" </> "Context.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon" </> "Judgement" </> "Context.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon" </> "Judgement" </> "Context" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon" </> "Judgement" </> "Context" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon" </> "Base.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon" </> "Base.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon" </> "Origin.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon" </> "Origin.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered" </> "LambekGrishin" </> "ResMon" </> "Trans.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Ordered" </> "Lambek"        </> "ResMon" </> "Trans.agda"
                  ]
  }


--------------------------------------------------------------------------------
-- Make: Linear Lambek Grishin Calculus
--------------------------------------------------------------------------------

makeLinearLambekGrishin :: Mapping
makeLinearLambekGrishin  = Mapping
  { blacklist   = [ "⊗ᶜ" , "⊕ᶜ"  , "⊗ʷ" , "⊕ʷ" ]
  , textMapping = [ "Unrestricted" ==> "Linear" ]
  , fileMapping = [ srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Base.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Linear"       </> "LambekGrishin" </> "Base.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Normal" </> "Base.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Linear"       </> "LambekGrishin" </> "Normal" </> "Base.agda"
                  ]
  }

--------------------------------------------------------------------------------
-- Make: Unrestricted Lambek Grishin Calculus
--------------------------------------------------------------------------------

makeUnrestrictedLambekGrishin :: Mapping
makeUnrestrictedLambekGrishin  = Mapping
  { blacklist   = [ "⇐" , "⇛" , "d⇚⇒" ]
  , textMapping = [ "Ordered" ==> "Unrestricted" ]
  , fileMapping = [ srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Type.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Type" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Context.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Type" </> "Context.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Context" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Type" </> "Context" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Type" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Subtype.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Type" </> "Subtype.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Structure.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Structure.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Structure" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Structure" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Structure" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Structure" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered"      </> "LambekGrishin" </> "Judgement.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Unrestricted" </> "LambekGrishin" </> "Judgement.agda"
                  ]
  }

--------------------------------------------------------------------------------
-- Make: Unrestricted Lambek Grishin Calculus
--------------------------------------------------------------------------------

makeLambekGrishinWithUnits :: Mapping
makeLambekGrishinWithUnits  = Mapping
  { blacklist   = [ " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹" ]
  , textMapping = [ ]
  , fileMapping = [ srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Type.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Type.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Type" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Type" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Type" </> "Context.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Type" </> "Context.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Type" </> "Context" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Type" </> "Context" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Type" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Type" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Type" </> "Subtype.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Type" </> "Subtype.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Structure.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Structure.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Structure" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Structure" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Structure" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Structure" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin"            </> "Judgement.agda"
                ==> srcDir </> "Logic" </> "Classical" </> "Ordered" </> "LambekGrishin" </> "Unit" </> "Judgement.agda"
                  ]
  }

--------------------------------------------------------------------------------
-- Mapping: Lambda Calculus
--------------------------------------------------------------------------------

makeLambda :: Mapping
makeLambda  = Mapping
  { blacklist   = [ "⇐"  , "⊕"  , "⇛"  , "⇚"   , "□"  , "◇"
                  , " ₀" , "{₀" , "(₀" , "r₀⁰" , "m₀"
                  , "⁰ " , "⁰}" , "⁰)" , "r⁰₀" , "m⁰"
                  , " ₁" , "{₁" , "(₁" , "r₁¹" , "m₁"
                  , "¹ " , "¹}" , "¹)" , "r¹₁" , "m¹"
                  ]
  , textMapping = [ "LG"            ==> "Λ"
                  , "Classical"     ==> "Intuitionistic"
                  , "Ordered"       ==> "Unrestricted"
                  , "LambekGrishin" ==> "Lambda"
                  ]
  , fileMapping = [ srcDir </> "Logic" </> "Classical"      </> "Ordered"      </> "LambekGrishin" </> "Type.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda"        </> "Type.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Complexity.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda"        </> "Type" </> "Complexity.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Context.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda"        </> "Type" </> "Context.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Context" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda"        </> "Type" </> "Context" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Polarised.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda"        </> "Type" </> "Polarised.agda"
                  , srcDir </> "Logic" </> "Classical"      </> "Ordered"      </> "LambekGrishin" </> "Type" </> "Subtype.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda"        </> "Type" </> "Subtype.agda"
                  ]
  }


--------------------------------------------------------------------------------
-- Mapping: Linear Lambda Calculus
--------------------------------------------------------------------------------

makeLinearLambda :: Mapping
makeLinearLambda  = Mapping
  { blacklist   = [ "wᴸ₁" , "wᴸ" , "cᴸ₁" , "cᴸ" ]
  , textMapping = [ "Unrestricted" ==> "Linear"
                  ]
  , fileMapping = [ srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda" </> "Base.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Linear"       </> "Lambda" </> "Base.agda"
                  , srcDir </> "Logic" </> "Intuitionistic" </> "Unrestricted" </> "Lambda" </> "Permute.agda"
                ==> srcDir </> "Logic" </> "Intuitionistic" </> "Linear"       </> "Lambda" </> "Permute.agda"
                  ]
  }


-------------------------------------------------------------------------------
-- Utility: generate files from other files by restricting the allowed symbols
--          and renaming symbols
-------------------------------------------------------------------------------


clobber :: Mapping -> Action ()
clobber Mapping{..} = liftIO (removeFiles "." (map snd fileMapping))

run :: Mapping -> Rules ()
run Mapping{..} = do

  when (not . null $ fileMapping) $ do

    let wanted = map snd fileMapping
    let prefix = joinPath (foldl1 commonPrefix (map (splitPath . dropFileName) wanted))

    want wanted

    prefix <//> "*.agda" *> \out ->
      case lookup out (map swap fileMapping) of
        Nothing  -> putLoud $ "Error: invalid mapping for " ++ out
        Just src -> do
          need [src]
          liftIO $
            T.writeFile out . restrictSource textMapping blacklist =<< T.readFile src


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

commonPrefix :: (Eq e) => [e] -> [e] -> [e]
commonPrefix _ [] = []
commonPrefix [] _ = []
commonPrefix (x:xs) (y:ys)
  | x == y    = x : commonPrefix xs ys
  | otherwise = []
