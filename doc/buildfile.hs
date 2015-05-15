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
  [ "abstract"
  , "introduction"
  , "motivation"
  , "agda_tutorial"
  , "linguistic_data"
  ]

tocWith :: FilePath -> [FilePath]
tocWith ext = map (("_build" </>).(-<.> ext)) toc


main :: IO ()
main = shakeArgs shakeOptions
       {shakeFiles    = "_build"
       ,shakeProgress = progressSimple
       } $ do

  want ["_build/main.pdf", "_build/main.html", "wc"]

  -- Compile thesis to PDF
  "_build/main.pdf" %> \out -> do
    let src = out -<.> "tex"
    let lcl = dropBuild src
    need (tocWith "tex")
    need ["_build/preamble.tex", "_build/main.bib", src]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]
    command_ [Cwd "_build", EchoStdout False] "bibtex"   [dropExtension lcl]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]


  -- Compile thesis to TeX
  "_build/main.tex" %> \out -> do
    let src = out -<.> "lagda"
    need (tocWith "tex")
    need [src]
    cmd "lhs2TeX" "--agda" "-P" ":_build/" src "-o" out

  -- Compile thesis to HTML
  "_build/main.html" %> \out -> do
    let src = map (\fn -> "_build" </> fn -<.> "noimp") toc
    need src
    unit $ cmd "pandoc" "-s" "-N" "-S" "-f" "markdown" "-t" "html" src "-o" out

  -- Convert Literate Agda files to TeX
  tocWith "tex" |%> \out -> do
      let src = out -<.> "lagda"
      need [src]
      liftIO $ copyFile src out

  -- Convert files without implicit to Literate Agda
  tocWith "lagda" |%> \out -> do
      let src = out -<.> "noimp"
      need [src]
      cmd "pandoc" "--filter" "./pandoc_lhs2TeX.hs" "--no-highlight"
                   "-S" "-f" "markdown" "-t" "latex" src "-o" out

  -- Convert Markdown files to files without implicit arguments
  tocWith "noimp" |%> \out -> do
      let src = out -<.> "md"
      need [src]
      liftIO $ B.writeFile out . stripImplicit' =<< B.readFile src

  -- Copy Markdown files to _build
  map ("_build" </>) ["main.lagda","preamble.tex","*.md","*.fmt","*.bib"]
    |%> \out -> do
    let src = dropBuild out
    need [src]
    liftIO $ copyFile src out

  -- Clean by removing the _build directory.
  "clean" ~> do
    removeFilesAfter "_build" ["//*"]

  "open" ~> do
    need ["_build/main.html", "_build/main.pdf"]
    unit $ cmd "open" "_build/main.html"
    unit $ cmd "open" "_build/main.pdf"



  -- Perform a word count.
  "wc" ~>
    cmd "wc" (map (<.> "md") toc)


-- |Drop the _build/ directory from the path.
dropBuild :: FilePath -> FilePath
dropBuild out = joinPath (filter (/="_build/") (splitPath out))


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
