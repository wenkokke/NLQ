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
import           Debug.Trace (traceShow)
import           Development.Shake
import           Development.Shake.FilePath


main :: IO ()
main = shakeArgs shakeOptions $ do

  want ["src/Logic/Lambek/Type.agda"
       ,"src/Logic/Lambek/Type/Context.agda"
       ,"src/Logic/Lambek/Type/Context/Polarised.agda"
       ,"src/Logic/Lambek/Judgement.agda"
       ,"src/Logic/Lambek/Judgement/Context.agda"
       ,"src/Logic/Lambek/Judgement/Context/Polarised.agda"
       ,"src/Logic/Lambek/ResMon/Base.agda"
       ,"src/Logic/Lambek/ResMon/Derivation.agda"
       ,"src/Logic/Lambek/ResMon/Origin.agda"
       ,"src/Logic/Lambek/ResMon/Trans.agda"]

  "src/Logic/Lambek//*.agda" *> \target -> do
    let src = toLambekGrishin target
    need [src]
    liftIO $
      T.writeFile target . handle =<< T.readFile src


-- |Map a filename to a file in the Lambek Grishin sub-directory.
toLambekGrishin :: FilePath -> FilePath
toLambekGrishin  = joinPath . map go . splitDirectories
  where
    go "Lambek" = "LambekGrishin"
    go path     = path


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

  lines        = T.lines input
  groups       = L.splitWhen isBlank lines
  groups'      = map (filter (not . isBlank)) groups
  noIllegalTS  = filter (all (not . isIllegalTS)) groups'
  concatted    = L.intercalate [T.append (T.replicate 80 " ") "\n"] noIllegalTS
  markIllegal  = zip (map isLegal concatted) concatted
  markIllegal' :: [(Bool, Text)]
  markIllegal' = snd (L.mapAccumL go (True , 0) markIllegal)
    where go :: (Bool , Int) -> (Bool , Text) -> ((Bool , Int) , (Bool , Text))
          go (_     , iX) (False , lnY) = ((False , min iX (indent lnY)) , (False , lnY))
          go (True  , _ ) (True  , lnY) = ((True  ,         indent lnY ) , (True  , lnY))
          go (False , iX) (True  , lnY) = ((legal , iX) , (legal , lnY))
            where
              legal         = notDeeper && notWithClause
              notDeeper     = iX >= indent lnY
              notWithClause = "..." /= T.take 3 (T.stripStart lnY)
  stripMarked  = map snd (filter fst markIllegal')
  stripEnd     = map T.stripEnd stripMarked
  output       = T.unlines stripEnd
  replace1     = T.replace "LambekGrishin" "Lambek" output
  replace2     = T.replace "LG" "NL" replace1

  in replace2


-- |Get the indentation for a line.
indent :: Text -> Int
indent = T.length . T.takeWhile isSpace


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
