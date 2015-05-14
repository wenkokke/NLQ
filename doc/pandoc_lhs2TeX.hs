#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types


import Text.Pandoc.JSON


convert :: Block -> Block
convert (CodeBlock _ str) = RawBlock (Format "latex") (codeBlock str)
convert bl                = bl

codeBlock :: String -> String
codeBlock code = unlines ["\\begin{code}",code,"\\end{code}"]

main :: IO ()
main = toJSONFilter convert
