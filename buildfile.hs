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

    want ["main.pdf","slides.pdf"]

    -- compile slides.tex with PdfLaTeX
    toBuild "slides.pdf" %> \out -> do
      let
        src  = out -<.> "tex"
        lcl  = fromBuild src

      slidesFiles <- getDirectoryFiles "" slidesFileList
      need (toBuild <$> slidesFiles)

      command_ [Cwd "_build", EchoStdout True ] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]


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

    -- copy files into the _build directory
    let static = map toBuild (thesisFileList ++ slidesFileList)
    static |%> \out -> copyFile' (fromBuild out) out

    -- copy files out of the _build directory
    let result = [ "main.pdf" , "slides.pdf" ]
    result |%> \out -> copyFile' (toBuild out) out

    -- clean files by removing the _build directory
    phony "clean" $ do
      putNormal "Cleaning files in _build"
      removeFilesAfter "_build" ["//*"]
