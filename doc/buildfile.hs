#!/usr/bin/env runhaskell


import           Control.Arrow ((***))
import           Development.Shake
import           Development.Shake.FilePath
import           Data.String (IsString(..))
import           Data.Text (Text)
import qualified Data.Text    as T
import qualified Data.Text.IO as T


-- The sequences of generated files are as follows:
--
-- For compilation to TeX:
--
--   1. $file.lagda
--   2. _build/$file.md_lagda
--   3. _build/$file.md_noimp_lagda
--   5. _build/$file.tex_lagda
--   6. _build/main.tex
--   7. _build/main.pdf
--
-- For compilation to HTML
--
--   1. $file.lagda
--   2. _build/$file.md_lagda
--   3. _build/$file.md_noimp_lagda
--   5. _build/main.html_nofmt
--   6. _build/main.html
--


toc :: [FilePath]
toc =
  [ "abstract"
  , "substructural_logic"
  , "type_logical_grammar"
  , "lambek_grammar"
  ]


main :: IO ()
main = shakeArgs shakeOptions { shakeFiles = "_build" } $ do

  -- * top-level tasks

  "html" ~> do
    let src = toBuild "main.html"
    need [src]
    cmd "open" src

  "pdf" ~> do
    let src = toBuild "main.pdf"
    need [src]
    cmd "open" src

  "count" ~>
    cmd "wc" (map (<.> "lagda") toc)

  -- * compilation of main files

  toBuild "main.html" %> \out -> do
    let src = out -<.> "html_nofmt"
    need [src]
    liftIO $ T.writeFile out . formatHTML =<< T.readFile src

  toBuild "main.html_nofmt" %> \out -> do
    let ref = toBuild "references.md"
    let yml = out -<.> "yml"
    let src = tocWith "md_noimp_lagda"
    need (ref : yml : src)
    cmd "pandoc" "-F" "pandoc-citeproc" yml
                 "-F" "./pandoc_HTML.hs"
                 "-s" "-N" "-S"
                 "-f" "markdown"
                 "-t" "html"
                 src ref "-o" out

  toBuild "main.tex" %> \out -> do
    let src = out -<.> "lagda"
    need (tocWith "tex_lagda")
    writeFile' src mainFile
    cmd "lhs2TeX" "--agda" "-P" ":_build/" src "-o" out

  toBuild "main.pdf" %> \out -> do
    let src = out -<.> "tex"
    need [src, out -<.> "bib", toBuild "preamble.tex"]
    let local = fromBuild src
    command_ [Cwd "_build", EchoStdout False] "pdflatex" ["-draftmode", local]
    command_ [Cwd "_build", EchoStdout False] "bibtex"   [dropExtension local]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" ["-draftmode", local]
    command_ [Cwd "_build", EchoStdout False] "pdflatex" [local]


  -- * compilation of auxiliary files

  -- generate references file
  toBuild "references.md" %> \out ->
    writeFile' out "# References\n"

  -- compile BibTeX file to YAML using pandoc-citeproc
  toBuild "main.yml" %> \out -> do
    let src = out -<.> "bib"
    need [src]
    Stdout yml <- cmd "pandoc-citeproc" "--bib2yaml" src
    writeFile' out yml

  -- import files by copying
  map toBuild ["preamble.tex","main.fmt","main.bib"] |%> \out -> do
    let src = fromBuild out
    copyFile' src out


  -- * compilation of auxiliary files by rules

  -- import Markdown/Literate Agda files
  tocWith "md_lagda" |%> \out -> do
    let src = fromBuild (out -<.> "lagda")
    copyFile' src out

  -- remove implicit arguments
  tocWith "md_noimp_lagda" |%> \out -> do
    let src = out -<.> "md_lagda"
    need [src]
    cmd "./remove_implicit_args.rb" src out

  -- compile Markdown to LaTeX in presence of literate Agda
  tocWith "tex_lagda_nopipe" |%> \out -> do
    let src = out -<.> "md_noimp_lagda"
    need [src]

    -- workaround: Pandoc will crash on empty files
    contents <- readFile' src
    if null contents
      then writeFile' out contents
      else cmd "pandoc" "-F" "./pandoc_lhs2TeX.hs"
                        "--natbib"
                        "--no-highlight"
                        "-S"
                        "-f" "markdown"
                        "-t" "latex"
                        src "-o" out

  -- fix a bug in Pandoc's output w.r.t. pipes
  tocWith "tex_lagda" |%> \out -> do
    let src = out -<.> "tex_lagda_nopipe"
    need [src]
    liftIO $ T.writeFile out . pandocFixPipe =<< T.readFile src


  "clean" ~>
    removeFilesAfter "_build" ["//*"]




-- * Path management

tocWith :: FilePath -> [FilePath]
tocWith ext = map (toBuild . (<.> ext)) toc

toBuild :: FilePath -> FilePath
toBuild = ("_build" </>)

fromBuild :: FilePath -> FilePath
fromBuild out = joinPath (filter (/="_build/") (splitPath out))


-- * Formatting of specific sequences


formatTeX :: Text -> Text
formatTeX = formatWith
  [
  ]


formatHTML :: Text -> Text
formatHTML = formatWith
  [ "|" ==> ""
  , "⇐" ==> "&#47;"
  , "⇒" ==> "&#92;"
  ]


pandocFixPipe :: Text -> Text
pandocFixPipe = formatWith
  [ "\\textbar{}" ==> "|"
  ]


formatWith :: [(String, String)] -> Text -> Text
formatWith =
  foldr ((\(pat,sub) -> (T.replace pat sub .)) . (fromString *** fromString)) id


(==>) :: a -> b -> (a , b)
(==>) = (,)


-- * Creating `main.lagda`

mainFile :: String
mainFile = unlines
  [ "\\documentclass{article}"
  , "%include main.fmt"
  , "\\include{preamble}%"
  , "\\begin{document}"
  , "\\begin{abstract}"
  , "%include abstract.tex_lagda"
  , "\\end{abstract}"
  , include_all_files
  , "\\nocite{*}%"
  , "\\bibliographystyle{apalike}%"
  , "\\bibliography{main}"
  , "\\end{document}"
  ]
  where
    include_all_files
      = unlines
      $ map ("%include " ++)
      $ filter (/="abstract.tex_lagda")
      $ tocWith "tex_lagda"
