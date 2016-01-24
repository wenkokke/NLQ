#!/usr/bin/env runhaskell

-- 1. create _build
-- 2. move all items into _build

import Development.Shake
import Development.Shake.FilePath


toBuild,fromBuild :: FilePath -> FilePath
toBuild   src = "_build" </> src
fromBuild out = joinPath (filter (/="_build/") (splitPath out))

thesisFileList :: [FilePattern]
thesisFileList =
  [ "main.tex"
  , "introduction.tex"
  , "display-calculus.tex"
  , "lexical-ambiguity.tex"
  , "natural-language-monads-and-effects.tex"
  , "logical-approaches-to-movement.tex"
  , "future-work.tex"
  , "main.bib"
  , "preamble.tex"
  , "fig-*.tex"
  , "cover.png"
  ]

slidesFileList :: [FilePattern]
slidesFileList =
  [ "slides.tex"
  , "main.bib"
  , "preamble.tex"
  , "lambek.pdf"
  ]

main :: IO ()
main =
  shakeArgs shakeOptions { shakeFiles = "_build" } $ do

    want [ "main.pdf" ]

    -- compile main.tex with PdfLaTeX
    toBuild "main.pdf" %> \out -> do
      let
        src  = out -<.> "tex"
        lcl  = fromBuild src

      thesisFiles <- getDirectoryFiles "" thesisFileList
      need (toBuild <$> ("NLQ_Agda.pdf" : "NLQ_Haskell.pdf" : thesisFiles))

      command_ [Cwd "_build", EchoStdout True] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", WithStdout True] "bibtex"   [dropExtension lcl]
      command_ [Cwd "_build", WithStdout True] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", WithStdout True] "pdflatex" [lcl]

    -- compile slides.tex with PdfLaTeX
    toBuild "slides.pdf" %> \out -> do
      let
        src  = out -<.> "tex"
        lcl  = fromBuild src

      slidesFiles <- getDirectoryFiles "" slidesFileList
      need (toBuild <$> slidesFiles)

      command_ [Cwd "_build", EchoStdout True] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", WithStdout True] "pdflatex" [lcl]

    -- compile NLQ_Agda.lagda with Agda
    toBuild "NLQ_Agda.pdf" %> \out -> do
      let
        src = toBuild "NLQ_Agda.processed.pdf"
      copyFile' src out

    toBuild "NLQ_Agda.processed.pdf" %> \out -> do
      let
        src = out -<.> "tex"
        lcl = fromBuild src

      need [src, toBuild "agda.sty"]
      command_ [Cwd "_build", EchoStdout True] "pdflatex" [lcl]

    toBuild "NLQ_Agda.processed.tex" %> \out -> do
      let
        src    = toBuild "NLQ_Agda.tex"
        script = "remove_implicit_args.rb"
      need [ src, script ]
      command_ [Cwd ".", WithStdout True] "ruby" [ script , "tex" , src , out ]

    toBuild <$> ["NLQ_Agda.tex", "agda.sty"] |%> \out -> do
      need ["NLQ_Agda.lagda"]
      command_ [Cwd ".", EchoStdout True] "agda"
        ["--latex"
        ,"--latex-dir=_build"
        ,"-i."
        ,"-i/usr/local/lib/agda/src"
        ,"NLQ_Agda.lagda"
        ]

    -- compile NLQ_Haskell.lhs with lhs2TeX
    toBuild "NLQ_Haskell.pdf" %> \out -> do
      let
        src = out -<.> "tex"
        lcl = fromBuild src

      need [src]
      command_ [Cwd "_build", EchoStdout True] "pdflatex" [lcl]

    toBuild "NLQ_Haskell.tex" %> \out -> do
      let src = fromBuild (out -<.> "lhs")
      need [src]
      command_ [Cwd ".", EchoStdout True] "lhs2TeX" [src,"-o",out]

    -- copy files into the _build directory
    let static = map toBuild (thesisFileList ++ slidesFileList)
    static |%> \out -> copyFile' (fromBuild out) out

    -- copy files out of the _build directory
    let result = [ "thesis.pdf" , "main.pdf" , "slides.pdf" , "NLQ_Agda.pdf" , "NLQ_Haskell.pdf" ]
    result |%> \out -> copyFile' (toBuild out) out

    -- clean files by removing the _build directory
    phony "clean" $ do
      putNormal "Cleaning files in _build"
      removeFilesAfter "_build" ["//*"]
