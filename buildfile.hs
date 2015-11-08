#!/usr/bin/env runhaskell

-- 1. create _build
-- 2. move all items into _build

import Development.Shake
import Development.Shake.FilePath


toBuild,fromBuild :: FilePath -> FilePath
toBuild   src = "_build" </> src
fromBuild out = joinPath (filter (/="_build/") (splitPath out))


main :: IO ()
main =
  shakeArgs shakeOptions { shakeFiles = "_build" } $ do

    want ["main.pdf"]

    -- compile main.tex with PdfLaTeX
    toBuild "main.pdf" %> \out -> do
      let
        src  = out -<.> "tex"
        lcl  = fromBuild src

      figs <- getDirectoryFiles "" ["fig-*.tex"]
      need (toBuild <$> ["main.tex" , "main.bib", "preamble.tex"] ++ figs)

      command_ [Cwd "_build", EchoStdout True ] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", EchoStdout False] "bibtex"   [dropExtension lcl]
      command_ [Cwd "_build", EchoStdout False] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", EchoStdout False] "pdflatex" [lcl]

    -- copy files into the _build directory
    let static = map toBuild $
          [ "main.tex"
          , "main.bib"
          , "preamble.tex"
          , "fig-*.tex"
          ]
    static |%> \out -> do
      copyFile' (fromBuild out) out

    -- copy files out of the _build directory
    let result =
          [ "main.pdf"
          ]
    result |%> \out -> do
      copyFile' (toBuild out) out

    -- clean files by removing the _build directory
    phony "clean" $ do
      putNormal "Cleaning files in _build"
      removeFilesAfter "_build" ["//*"]
