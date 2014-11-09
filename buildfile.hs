#!/usr/bin/env runhaskell

{-# LANGUAGE OverloadedStrings #-}

import           Data.Attoparsec.Text (Parser)
import qualified Data.Attoparsec.Text as P
import           Data.Char as C (isSpace)
import           Data.Either (isRight)
import qualified Data.List as L
import qualified Data.List.Split as L (splitWhen)
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Development.Shake
import           Development.Shake.FilePath


main :: IO ()
main = shakeArgs shakeOptions $ do

  want (map toLambek ["Base","Derivation","Origin","Trans"])

  toLambek "*" *> \target -> do
    let src = toLambekGrishin target
    need [src]
    liftIO $
      T.writeFile target . handle =<< T.readFile src


-- |Map a filename to a file in the Lambek sub-directory.
toLambek :: FilePath -> FilePath
toLambek file = "src/Logic/Lambek/ResMon" </> takeFileName file -<.> "agda"


-- |Map a filename to a file in the Lambek Grishin sub-directory.
toLambekGrishin :: FilePath -> FilePath
toLambekGrishin file = "src/Logic/LambekGrishin/ResMon" </> takeFileName file -<.> "agda"


-- |Parse a file and remove all groups which contain illegal symbols.
handle :: Text -> Text
handle input = let

  -- The idea is to get the groups separated by blank lines and then
  -- delete the entire group when it contains a type signature
  -- containing one or more of the blacklisted terms.
  -- In all other case, it will only erase the line.
  --
  -- The reason I feel that this is a sensible algorithm is that it
  -- promotes a sensible coding style (separating definitions by a
  -- blank line, and keeping documentation connected to the functions).
  lines    = T.lines input
  groups   = L.splitWhen isBlank lines
  filter1  = filter (all (not . isIllegalTS)) groups
  filter2  = map (filter isLegal) filter1
  output   = T.unlines (L.intersperse "\n" (map T.unlines filter2))

  in output


-- |Check if a text is completely blank.
isBlank :: Text -> Bool
isBlank = T.all isSpace


-- |Check if text is a type signature containing blacklisted items.
isIllegalTS :: Text -> Bool
isIllegalTS = isRight . P.parseOnly p
  where
    p :: Parser ()
    p = do
      P.takeWhile (not . isSpace)
      P.space
      P.many1 (P.char ':')
      rest <- P.takeText
      if isLegal rest
        then fail "Type signature contains no blacklisted items."
        else return ()


-- |Check if text contains any blacklisted items.
isLegal :: Text -> Bool
isLegal  = not . foldr (\x f y -> f y || x `T.isInfixOf` y) (const False) blacklist


-- |Set of inference rules which may not occur in the Lambek calculus.
blacklist :: [Text]
blacklist =
  [ "⊕"      , "⇛"      , "⇚"
--, "mon-⊕"  , "mon-⇛"  , "mon-⇚"
--, "res-⇛⊕" , "res-⊕⇛" , "res-⊕⇚" , "res-⇚⊕"
  , "grish₁" , "grish₂" , "grish₃" , "grish₄"
 ]
