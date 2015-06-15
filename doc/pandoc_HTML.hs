#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types


import Text.Pandoc.JSON


convert :: Block -> Block
convert bl@(CodeBlock (id, classes, kv) str)
  | "hidden" `elem` classes = Null
  | otherwise               = CodeBlock (id, "agda" : classes, kv) str
convert bl                  = bl


main :: IO ()
main = toJSONFilter convert
