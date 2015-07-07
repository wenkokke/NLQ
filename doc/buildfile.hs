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
--   5. _build/$file.lagda
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
  , "int_introduction"
  , "int_categorial_grammar"
  , "int_substructural_logic"
  , "nl_base"
  , "nl_ll_base"
  , "nl_derivational_semantics"
  , "nl_display_calculus"
  , "nl_spurious_ambiguity"
  , "nl_focusing_and_polarity"
  , "nl_cps_base"
  , "nl_cps_translation"
  , "ext_categorial_grammar"
  , "ext_lg_base"
  ]


main :: IO ()
main = shakeArgs shakeOptions { shakeFiles = "_build" } $ do

  -- * top-level tasks

  want ["pdf"]

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
    need (tocWith "lagda")
    need [toBuild "main.fmt"]
    writeFile' src mainFile_lhs2TeX
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
    need [src]
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
  tocWith "lagda_nopipe" |%> \out -> do
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
  tocWith "lagda" |%> \out -> do
    let src = out -<.> "lagda_nopipe"
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

mainFile_agda :: String
mainFile_agda =
  mainFile
  "\\usepackage{agda}%"
  (\fn -> "\\input{"++(fn <.> "tex")++"}")

mainFile_lhs2TeX :: String
mainFile_lhs2TeX =
  mainFile
  "%include main.fmt"
  (\fn -> "%include "++toBuild (fn <.> "lagda"))

mainFile :: String -> (String -> String) -> String
mainFile importFile input = unlines
  [ "\\documentclass[usenames]{article}"
  , importFile
  , "\\include{preamble}%"
  , "\\begin{document}"
  , "\\begin{abstract}"
  , input "abstract"
  , "\\end{abstract}"
  , "\\tableofcontents%"
  , "\\newpage%"
  , include_all_files
  , "\\nocite{*}%"
  , "\\bibliographystyle{apalike}%"
  , "\\bibliography{main}"
  , "\\end{document}"
  ]
  where
    include_all_files
      = unlines (map input (filter (/="abstract") toc))
