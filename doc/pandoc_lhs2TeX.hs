#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types
--   * process


import AgdaUtil
import Control.Monad (filterM)
import System.Directory (doesFileExist)
import System.FilePath ((</>),isRelative)
import Text.Pandoc.JSON
import Text.Pandoc.Walk


-- | Convert code blocks to LaTeX code blocks.
convertCode :: Block -> Block
convertCode (CodeBlock (_, classes, _) str)
   | "hidden"  `elem` classes = RawBlock (Format "latex") (hideEnv (codeEnv str))
   | "partial" `elem` classes = RawBlock (Format "latex") (partEnv (codeEnv str))
   | otherwise                = RawBlock (Format "latex")          (codeEnv str)
  where
  codeEnv str = unlines ["\\begin{code}"     , str, "\\end{code}"]
  partEnv str = unlines ["\\begin{truncated}", str, "\\end{truncated}"]
  hideEnv str = unlines ["\\begin{comment}"  , str, "\\end{comment}"]
convertCode bl                   = bl


-- | Disambiguate a filepath.
disambLink :: FilePath -> IO FilePath
disambLink file = do
  candidate_dirs  <- agda_path
  candidate_files <- filterM doesFileExist (map (</> file) candidate_dirs)
  if length candidate_files == 1
    then return (head candidate_files)
    else error ("disambLink: ambiguous filepath "++show file
                ++", could refer to any of "++show candidate_files)


-- | Evaluate Agda links and replace them with their result.
convertLink :: Inline -> IO Inline
convertLink (Link [Str "compute"] (file, expr)) = do
  file' <- if isRelative file then disambLink file else return file
  resl  <- compute_toplevel file' [expr]
  case resl of
    []    -> fail ("compute_toplevel: error in evaluating `" ++ expr ++ "'")
    (x:_) -> return (RawInline (Format "latex") x)
convertLink inl = return inl


main :: IO ()
main = toJSONFilter
     $ (walkM convertLink :: Pandoc -> IO Pandoc)
     . (walk  convertCode :: Pandoc ->    Pandoc)
