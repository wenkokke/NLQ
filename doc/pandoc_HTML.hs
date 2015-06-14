#!/usr/bin/env runhaskell


-- cabal depedencies:
--
--   * containers
--   * pandoc-types


import Text.Pandoc.JSON


convert :: Block -> Block
convert bl@(CodeBlock (_, classes, _) _)
  | "hidden" `elem` classes = Null
  | otherwise               = bl
convert bl                  = bl


main :: IO ()
main = toJSONFilter convert
