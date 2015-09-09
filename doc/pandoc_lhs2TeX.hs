#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types
--   * process


import AgdaUtil (resolvePath,computeTopLevel)
import Data.Hashable (hash)
import System.Directory (getModificationTime)
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


-- | Evaluate Agda links and replace them with their result.
convertLink :: Inline -> IO Inline
convertLink (Link [Str "compute"] (file, expr)) = do
  path <- resolvePath file
  resl <- computeTopLevel path [expr]
  case resl of
    []    -> fail ("compute_toplevel: error in evaluating `" ++ expr ++ "'")
    (x:_) -> return (RawInline (Format "latex") x)
convertLink inl = return inl


main :: IO ()
main = toJSONFilter
     $ (walkM convertLink :: Pandoc -> IO Pandoc)
     . (walk  convertCode :: Pandoc ->    Pandoc)
