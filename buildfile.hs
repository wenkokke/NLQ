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
  , "main.bib"
  , "preamble.tex"
  , "fig-*.tex"
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

    -- compile thesis.pdf from several files
    toBuild "thesis.pdf" %> \out -> do
      need (toBuild <$> [ "main.pdf", "NLPlus.pdf" ])
      command_ [Cwd "_build", EchoStdout True] "gs"
        [ "-o", "thesis.pdf"
        , "-sDEVICE=pdfwrite"
        , "-dPDFSETTINGS=/prepress"
        , "main.pdf"
        , "NLPlus.pdf"
        ]

    -- compile main.tex with PdfLaTeX
    toBuild "main.pdf" %> \out -> do
      let
        src  = out -<.> "tex"
        lcl  = fromBuild src

      thesisFiles <- getDirectoryFiles "" thesisFileList
      need (toBuild <$> thesisFiles)

      command_ [Cwd "_build", EchoStdout True ] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", EchoStdout False] "bibtex"   [dropExtension lcl]
      command_ [Cwd "_build", EchoStdout False] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]

    -- compile slides.tex with PdfLaTeX
    toBuild "slides.pdf" %> \out -> do
      let
        src  = out -<.> "tex"
        lcl  = fromBuild src

      slidesFiles <- getDirectoryFiles "" slidesFileList
      need (toBuild <$> slidesFiles)

      command_ [Cwd "_build", EchoStdout True] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", WithStdout True] "pdflatex" [lcl]

    -- compile NLPlus.lagda with Agda
    toBuild "NLPlus.pdf" %> \out -> do
      let
        src = toBuild "NLPlus.processed.pdf"
      copyFile' src out

    toBuild "NLPlus.processed.pdf" %> \out -> do
      let
        src = out -<.> "tex"
        lcl = fromBuild src

      need [src, toBuild "agda.sty"]
      command_ [Cwd "_build", EchoStdout True] "pdflatex" [lcl]

    toBuild "NLPlus.processed.tex" %> \out -> do
      let
        src    = toBuild "NLPlus.tex"
        script = "remove_implicit_args.rb"
      need [ src, script ]
      command_ [Cwd ".", WithStdout True] "ruby" [ script , "tex" , src , out ]

    toBuild <$> ["NLPlus.tex", "agda.sty"] |%> \out -> do
      need ["NLPlus.lagda"]
      command_ [Cwd ".", EchoStdout True] "agda"
        ["--latex"
        ,"--latex-dir=_build"
        ,"-i."
        ,"-i/usr/local/Cellar/agda/2.4.2.4_2/agda-stdlib/src"
        ,"NLPlus.lagda"
        ]

    -- copy files into the _build directory
    let static = map toBuild (thesisFileList ++ slidesFileList)
    static |%> \out -> copyFile' (fromBuild out) out

    -- copy files out of the _build directory
    let result = [ "thesis.pdf" , "main.pdf" , "slides.pdf" , "NLPlus.pdf" ]
    result |%> \out -> copyFile' (toBuild out) out

    -- clean files by removing the _build directory
    phony "clean" $ do
      putNormal "Cleaning files in _build"
      removeFilesAfter "_build" ["//*"]
