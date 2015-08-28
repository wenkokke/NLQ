#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types
--   * process


import Text.Pandoc.JSON


-- | Convert code blocks to LaTeX code blocks.
convertCode :: Block -> Block
convertCode (CodeBlock (_, classes, _) str)
   | "hidden"  `elem` classes = RawBlock (Format "latex") (hideEnv (codeEnv str))
   | "partial" `elem` classes = RawBlock (Format "latex") (partEnv (codeEnv str))
   | otherwise                = RawBlock (Format "latex")          (codeEnv str)
  where
  codeEnv str = unlines ["\\begin{code}",str,"\\end{code}"]
  partEnv str = unlines ["\\begin{truncated}",str,"\\end{truncated}"]
  hideEnv str = unlines ["\\begin{comment}",str,"\\end{comment}"]
convertCode bl                   = bl


main :: IO ()
main = toJSONFilter convertCode
