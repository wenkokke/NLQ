#!/usr/bin/env runhaskell


import           Control.Arrow ((***))
import           Control.Monad (forM_)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as Lazy
import qualified Data.ByteString.UTF8 as B (fromString)
import qualified Data.ByteString.Search as B (replace)
import           Development.Shake
import           Development.Shake.FilePath
import           Text.Regex.PCRE (Regex,makeRegex,matchOnceText)
import           Text.Regex.PCRE.ByteString ()
import           System.Directory (copyFile)


toc :: [FilePath]
toc =
  [ "ab_grammars"
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
    need ["_build/preamble.tex", "_build/main.bib", "_build/main.fmt", src]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" ["-draftmode", lcl]
    command_ [Cwd "_build", EchoStdout False] "bibtex"   [dropExtension lcl]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" ["-draftmode", lcl]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]


  -- Compile thesis to TeX
  "_build/main.tex" %> \out -> do
    let src = out -<.> "lagda"
    need (tocWith "tex")
    need [src]
    cmd "lhs2TeX" "--agda" "-P" ":_build/" src "-o" out

  -- Compile thesis to HTML
  "_build/main.html" %> \out -> do
    let src = tocWith "no_implicit_args"
    let ref = "_build/references.md"
    let bib = out -<.> "yml"
    let tmp = tocWith "replace_for_html"
    need (bib : src)
    writeFile' ref "# References\n"
    liftIO $
      forM_ tmp $ \fn ->
        B.writeFile fn . format formatListHTML
          =<< B.readFile (fn -<.> "no_implicit_args")
    unit $
      cmd "pandoc" "-F" "pandoc-citeproc" bib
                 "-s" "-N" "-S"
                 "-f" "markdown"
                 "-t" "html"
                 tmp ref "-o" out


  -- Compile bibliography to YAML
  "_build/main.yml" %> \out -> do
    let src = out -<.> "bib"
    need [src]
    Stdout yml <- cmd "pandoc-citeproc" "--bib2yaml" src
    writeFile' out yml

  -- Convert Literate Agda files to TeX
  tocWith "tex" |%> \out -> do
    let src = out -<.> "lagda"
    need [src]
    liftIO $ copyFile src out

  -- Convert files without implicit to Literate Agda
  tocWith "lagda" |%> \out -> do
    let src = out -<.> "no_implicit_args"
    let tmp = out -<.> "replace_for_latex"
    need [src]
    liftIO $
      B.writeFile tmp . format formatListLaTeX =<< B.readFile src
    cmd "pandoc" "-F" "./pandoc_lhs2TeX.hs"
                 "--natbib"
                 "--no-highlight"
                 "-S"
                 "-f" "markdown"
                 "-t" "latex"
                 tmp "-o" out

  -- Convert Markdown files to files without implicit arguments
  tocWith "no_implicit_args" |%> \out -> do
    let src = out -<.> "md"
    need [src]
    liftIO $ B.writeFile out . stripImplicit =<< B.readFile src

  -- Copy Markdown files to _build
  map ("_build" </>) ["main.lagda","preamble.tex","*.md","*.fmt","*.bib"]
    |%> \out -> do
    let src = dropBuild out
    need [src]
    liftIO $ copyFile src out

  -- Clean by removing the _build directory.
  "clean" ~> do
    removeFilesAfter "_build" ["//*"]

  "pdf" ~> do
    need ["_build/main.pdf"]
    unit $ cmd "open" "_build/main.pdf"

  "html" ~> do
    need ["_build/main.html"]
    unit $ cmd "open" "_build/main.html"



  -- Perform a word count.
  "wc" ~>
    cmd "wc" (map (<.> "md") toc)


-- |Drop the _build/ directory from the path.
dropBuild :: FilePath -> FilePath
dropBuild out = joinPath (filter (/="_build/") (splitPath out))



-- * Formatting directives for HTML

format :: [(ByteString, ByteString)] -> ByteString -> ByteString
format = foldr (\(pat,sub) -> ((Lazy.toStrict . B.replace pat sub) . )) id

formatListLaTeX :: [(ByteString, ByteString)]
formatListLaTeX = map (B.fromString *** B.fromString)
  [ ("⇒" , "\\varbslash" )
  , ("⇐" , "\\varslash"  )
  ]

formatListHTML :: [(ByteString, ByteString)]
formatListHTML = map (B.fromString *** B.fromString)
  [ ("⇒" , "\\backslash" )
  , ("⇐" , "/"           )
  ]


-- * Stripping implicit characters

-- |Regular expression to match implicit arguments in Agda.
reAgdaImplicit :: Regex
reAgdaImplicit =
  makeRegex "(?<!record)(?<!λ)(\\s*(∀\\s*)?\\{([^=^\\}]*)\\}(\\s*→)?)"


-- |Byte strings for @\begin{code}@, @\end{code}@ and @%include@.
beginCode, endCode, codeFence :: ByteString
beginCode = B.fromString "\\begin{code}"
endCode   = B.fromString "\\end{code}"
codeFence = B.fromString "```"

-- |Strip implicit arguments from the given byte string, checking
--  whether they are contained within @\begin{code}@ and @\end{code}@ tags.
stripImplicitTeX :: ByteString -> ByteString
stripImplicitTeX str
  | B.null rest = str
  | otherwise   = B.append (B.append pref (handle code)) (stripImplicit suff)
  where
    (pref,rest) = B.breakSubstring beginCode str
    (code,suff) = B.breakSubstring endCode rest
    handle code = B.append beginCode (unsafeStripImplicit (B.drop (B.length beginCode) code))


-- |As @stripImplicit@, but for code contained within Markdown code
--  fences (i.e. "```").
stripImplicitMd :: ByteString -> ByteString
stripImplicitMd str
  | B.null rest = str
  | otherwise   = B.append (B.append pref (handle code)) (stripImplicit suff)
  where
    (pref,rest) = B.breakSubstring codeFence str
    (code,suff) = B.breakSubstring codeFence rest
    handle code = unsafeStripImplicit (B.drop (B.length codeFence) code)


-- |Combination of @stripImplicitMd and @stripImplicitTeX@.
stripImplicit :: ByteString -> ByteString
stripImplicit = stripImplicitTeX . stripImplicitMd


-- |Strip all implicit arguments from the given byte string.
unsafeStripImplicit :: ByteString -> ByteString
unsafeStripImplicit str = case matchOnceText reAgdaImplicit str of
  Just (a,_,b) -> B.append a (unsafeStripImplicit b)
  _            -> str
