#!/usr/bin/env runhaskell


import           Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.UTF8 as B (fromString)
import           Development.Shake
import           Development.Shake.FilePath
import           Text.Regex.PCRE
import           Text.Regex.PCRE.ByteString ()
import           System.Directory (copyFile)


toc :: [FilePath]
toc =
  [ "motivation"
  , "agda_tutorial"
  ]


main :: IO ()
main = shakeArgs shakeOptions
       {shakeFiles    = "_build"
       ,shakeProgress = progressSimple
       } $ do

  want ["_build/main.pdf", "_build/main.html"]


  -- Compile thesis to PDF
  "_build/main.pdf" %> \out -> do
    let src = out -<.> "tex"
    need (map (\fn -> "_build" </> fn -<.> "tex") toc)
    need ["_build/preamble.tex", src]
    unit $ cmd "pdflatex" "-output-directory" "_build" src
    unit $ cmd "open" "_build/main.pdf"

  -- Convert files without implicit arguments to HTML
  "_build/main.html" %> \out -> do
    let src = map (\fn -> "_build" </> fn -<.> "noimp") toc
    need src
    unit $ cmd "pandoc" "-s" "-f" "markdown" "-t" "html" src "-o" out
    unit $ cmd "open" "_build/main.html"

  -- Convert Literate Agda files to TeX
  "_build//*.tex" %> \out ->
    checkIfExist out $ do
      let src = out -<.> "lagda"
      need [src]
      if out == "_build/main.tex"
        then do
          contents <- liftIO (B.readFile src)
          if beginCode `B.isInfixOf` contents
            || include `B.isInfixOf` contents
            then cmd "lhs2TeX" "--agda" "-P" ":_build/" src "-o" out
            else liftIO (copyFile src out)
        else liftIO (copyFile src out)

  -- Convert files without implicit to Literate Agda
  "_build//*.lagda" %> \out -> do
    checkIfExist out $ do
      let src = out -<.> "noimp"
      need [src]
      cmd "pandoc" "--filter" "./pandoc_lhs2TeX.hs" "--no-highlight" "-f" "markdown" "-t" "latex" src "-o" out

  -- Convert Markdown files to files without implicit arguments
  "_build//*.noimp" %> \out -> do
    checkIfExist out $ do
      let src = out -<.> "md"
      need [src]
      liftIO $
        B.writeFile out . stripImplicit' =<< B.readFile src

  -- Copy Markdown files to _build
  ["_build//*.md", "_build//*.fmt"] |%> \out -> do
    checkIfExist out (return ())

  -- Clean by removing the _build directory.
  "clean" ~> do
    removeFilesAfter "_build" ["//*"]


-- |Check if a file exists outside of the _build directory and--if
--  so--simply copy it into the _build directory. Otherwise, run the
--  given continuation.
checkIfExist :: FilePath -> Action () -> Action ()
checkIfExist out cont = do
  let src = joinPath (filter (/="_build/") (splitPath out))
  srcExist <- doesFileExist src
  if srcExist
    then need [src] >> liftIO (copyFile src out)
    else cont


-- |Regular expression to match implicit arguments in Agda.
reAgdaImplicit :: Regex
reAgdaImplicit =
  makeRegex "(?<!record)(?<!λ)(\\s*(∀\\s*)?\\{([^=^\\}]*)\\}(\\s*→)?)"


-- |Byte strings for @\begin{code}@, @\end{code}@ and @%include@.
beginCode, endCode, include, codeFence :: ByteString
beginCode = B.fromString "\\begin{code}"
endCode   = B.fromString "\\end{code}"
include   = B.fromString "%include"
codeFence = B.fromString "```"


-- |Strip all implicit arguments from the given byte string, not
--  checking whether or not they are contained within @\begin{code}@
--  and @\end{code}@ tags.
unsafeStripImplicit :: ByteString -> ByteString
unsafeStripImplicit str = case matchOnceText reAgdaImplicit str of
  Just (a,_,b) -> B.append a (unsafeStripImplicit b)
  _            -> str


-- |Strip implicit arguments from the given byte string, checking
--  whether they are contained within @\begin{code}@ and @\end{code}@ tags.
stripImplicit :: ByteString -> ByteString
stripImplicit str
  | B.null rest = str
  | otherwise   = B.append (B.append pref (handle code)) (stripImplicit suff)
  where
    (pref,rest) = B.breakSubstring beginCode str
    (code,suff) = B.breakSubstring endCode rest
    handle code = B.append beginCode (unsafeStripImplicit (B.drop (B.length beginCode) code))


-- |Strip implicit arguments from the given byte string, checking
--  whether they are contained within @\begin{code}@ and @\end{code}@ tags.
stripImplicit' :: ByteString -> ByteString
stripImplicit' str
  | B.null rest = str
  | otherwise   = B.append (B.append pref (handle code)) (stripImplicit suff)
  where
    (pref,rest) = B.breakSubstring codeFence str
    (code,suff) = B.breakSubstring codeFence rest
    handle code = unsafeStripImplicit (B.drop (B.length codeFence) code)
