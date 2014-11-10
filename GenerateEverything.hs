#!/usr/bin/env runhaskell

{-# LANGUAGE PatternGuards #-}

import qualified Data.List as L -- package: base
import Control.Applicative      -- *
import System.Environment       -- *
import System.IO                -- *
import System.Exit              -- *
import System.FilePath          -- package: filepath
import System.FilePath.Find     -- package: filemanip


headerFile,outputFile,srcDir :: String
headerFile = "Header"
outputFile = "src/Everything.agda"
srcDir     = "src"


main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  header  <- readFileUTF8 headerFile
  modules <- L.sort <$>
               find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    srcDir
  headers <- mapM extractHeader modules

  writeFileUTF8 outputFile $
    header ++ format (zip modules headers)


-- | Usage info.
usage :: String
usage = unlines
  [ "GenerateEverything: A utility program for Agda's standard library."
  , ""
  , "Usage: GenerateEverything"
  , ""
  , "This program should be run in the base directory of a clean checkout of"
  , "the library."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to " ++ outputFile
  , "with the file " ++ headerFile ++ " inserted verbatim at the beginning."
  ]


-- | Reads a module and extracts the header.
extractHeader :: FilePath -> IO [String]
extractHeader file = fmap (extract . lines) $ readFileUTF8 file
  where
  delimiter = all (== '-')

  extract (d1 : "-- The Lambek Calculus in Agda" : "--" : ss)
    | delimiter d1
    , (info, d2 : _) <- span (\ln -> "--" `L.isPrefixOf` ln
                             && not ("---" `L.isPrefixOf` ln)) ss
    , delimiter d2
    = info
  extract _ = error $ file ++ " is malformed."


-- | Formats the extracted module information.
format :: [(FilePath, [String])]
          -- ^ Pairs of module names and headers. All lines in the
          -- headers are already prefixed with \"-- \".
       -> String
format = unlines . concatMap fmt
  where
  fmt (file, header) = sep : header ++ ["import " ++ fileToMod file]
    where
      sep | '.' `elem` file = ""
          | otherwise       = "\n"


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
