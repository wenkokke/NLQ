#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types


import Text.Pandoc.JSON


convert :: Block -> Block
convert (CodeBlock (_, classes, _) str)
  | "hidden"  `elem` classes = RawBlock (Format "latex") (hideEnv (codeEnv str))
  | "partial" `elem` classes = RawBlock (Format "latex") (partEnv (codeEnv str))
  | otherwise                = RawBlock (Format "latex")          (codeEnv str)
convert bl                   = bl


codeEnv :: String -> String
codeEnv str = unlines ["\\begin{code}",str,"\\end{code}"]


partEnv :: String -> String
partEnv str = unlines ["\\begin{truncated}",str,"\\end{truncated}"]


hideEnv :: String -> String
hideEnv str = unlines ["\\begin{comment}",str,"\\end{comment}"]


main :: IO ()
main = toJSONFilter convert
