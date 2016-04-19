#!/usr/bin/env runhaskell

-- 1. create _build
-- 2. move all items into _build

import Development.Shake
import Development.Shake.FilePath


local :: FilePath -> FilePath
local out = joinPath (filter (`notElem` ["_build/","src/","doc/"]) (splitPath out))

toBuild,toSrc,toDoc :: FilePath -> FilePath
toBuild = ("_build" </>) . local
toSrc   = ("src"    </>) . local
toDoc   = ("doc"    </>) . local

docFileList :: [FilePattern]
docFileList =
  [ "main.tex"
  , "introduction.tex"
  , "display-calculus.tex"
  , "lexical-ambiguity.tex"
  , "logical-approaches-to-movement.tex"
  , "future-work.tex"
  , "main.bib"
  , "preamble.tex"
  , "fig-*.tex"
  , "cover.png"
  ]

main :: IO ()
main =
  shakeArgs shakeOptions { shakeFiles = "_build" } $ do

    want [ "main.pdf" ]

    -- compile main.tex with PdfLaTeX
    toBuild "main.pdf" %> \out -> do
      let src  = toDoc out -<.> "tex"
          lcl  = local src

      docFiles <- getDirectoryFiles "doc" docFileList
      need (toBuild <$> ("NLQ_Agda.pdf" : "NLQ_Haskell.pdf" : docFiles))

      command_ [Cwd "_build", EchoStdout True] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", WithStdout True] "bibtex"   [dropExtension lcl]
      command_ [Cwd "_build", WithStdout True] "pdflatex" ["-draftmode", lcl]
      command_ [Cwd "_build", WithStdout True] "pdflatex" [lcl]

    -- compile NLQ_Agda.lagda with Agda
    toBuild "NLQ_Agda.pdf" %> \out -> do
      let src = toBuild "NLQ_Agda.processed.pdf"
      copyFile' src out

    toBuild "NLQ_Agda.processed.pdf" %> \out -> do
      let src = out -<.> "tex"
          lcl = local src

      need [src, toBuild "agda.sty"]
      command_ [Cwd "_build", EchoStdout True] "pdflatex" [lcl]

    toBuild "NLQ_Agda.processed.tex" %> \out -> do
      let src    = toBuild "NLQ_Agda.tex"
          script = "remove_implicit_args.rb"
      need [ src, script ]
      command_ [Cwd ".", WithStdout True] "ruby" [ script , "tex" , src , out ]

    toBuild <$> ["NLQ_Agda.tex", "agda.sty"] |%> \out -> do
      let src = toDoc "NLQ_Agda.lagda"
      need [src]
      command_ [Cwd ".", EchoStdout True] "agda"
        ["--latex"
        ,"--latex-dir=_build"
        ,"-idoc"
        ,"-i/usr/local/lib/agda/src"
        ,src
        ]

    -- compile NLQ_Haskell.lhs with lhs2TeX
    toBuild "NLQ_Haskell.pdf" %> \out -> do
      let src = out -<.> "tex"
          lcl = local src

      need [src]
      command_ [Cwd "_build", EchoStdout True] "pdflatex" [lcl]

    toBuild "NLQ_Haskell.tex" %> \out -> do
      let src = toDoc (out -<.> "lhs")

      need [src]
      command_ [Cwd ".", EchoStdout True] "lhs2TeX" [src,"-o",out]

    -- run the generated Haskell file
    "test" ~> do
      unit $ command_ [] "cabal" ["configure","--builddir=_build","--enable-tests"]
      unit $ command_ [] "cabal" ["install","--only-dependencies"]
      unit $ command_ [] "cabal" ["build"]
      unit $ command_ [] "cabal" ["test"]

    -- copy files into the _build directory
    let static = map toBuild docFileList
    static |%> \out -> copyFile' (toDoc out) out

    -- copy files out of the _build directory
    let result = [ "thesis.pdf" , "main.pdf" , "slides.pdf" , "NLQ_Agda.pdf" , "NLQ_Haskell.pdf" ]
    result |%> \out -> copyFile' (toBuild out) out

    -- clean files by removing the _build directory
    phony "clean" $ do
      putNormal "Cleaning files in _build"
      removeFilesAfter "_build" ["//*"]
      putNormal "Cleaning files in dist"
      removeFilesAfter "dist" ["//*"]
      putNormal "Cleaning files in auto"
      removeFilesAfter "auto" ["//*"]
      putNormal "Cleaning temporary Agda files"
      removeFilesAfter "." [toDoc "NLQ_Agda.agdai"]
      putNormal "Cleaning temporary Haskell files"
      removeFilesAfter "." [toDoc "NLQ_Haskell.hi",toDoc "NLQ_Haskell.o"]
