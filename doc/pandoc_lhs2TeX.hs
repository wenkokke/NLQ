#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types


import Text.Pandoc.JSON


convert :: Block -> Block
convert bl@(CodeBlock (_, classes, _) str)
  | "hidden"  `elem` classes = Null
  | "partial" `elem` classes = RawBlock (Format "latex") (partEnv (codeEnv str))
  | otherwise                = RawBlock (Format "latex")          (codeEnv str)
convert bl                   = bl


codeEnv :: String -> String
codeEnv str = unlines ["\\begin{code}",str,"\\end{code}"]


partEnv :: String -> String
partEnv str = unlines ["\\begin{partial}",str,"\\end{partial}"]


main :: IO ()
main = toJSONFilter convert
