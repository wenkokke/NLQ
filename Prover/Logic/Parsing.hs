{-# LANGUAGE RecordWildCards #-}
module Logic.Parsing where


import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Void (Void)
import           Text.Parsec hiding (getInput)
import           Text.Parsec.Expr
import           Text.Parsec.Language (LanguageDef,haskellStyle)
import           Text.Parsec.Token (TokenParser,GenTokenParser(..),GenLanguageDef(..))
import qualified Text.Parsec.Token as P

import           Prover hiding (Term)
import           Logic.Base
import           Logic.Printing (Agda(..),ASCII(..))
import           Logic.DSL (down,fbin,sbin)


-- * Parsing formulas

atom :: Parsec String () (Term Void)
atom = (flip Con [] . Atom) <$> identifier <?> "atomic formulas"
  where
    TokenParser{..} = lexer


con :: ConId -> Parsec String () ()
con c = reservedOp (show (Agda c)) <|> reservedOp (show (ASCII c))
  where
    TokenParser{..} = lexer


lexicon :: Parsec String () (Map String (Term Void))
lexicon = M.fromList <$> many1 entry
  where
    TokenParser{..} = lexer

    entry = (,) <$> identifier <* symbol ":" <*> formula


formula :: Parsec String () (Term Void)
formula = buildExpressionParser table (parens formula <|> atom)
  where
    TokenParser{..} = lexer
    op   c = Infix   (con c >> return (fbin c))
    pre  c = Prefix  (con c >> return (\x -> Con c [x]))
    post c = Postfix (con c >> return (\x -> Con c [x]))
    table =
      [ [pre F0L , post F0R , pre F1L , post F1R
        ,pre FBox           , pre FDia           ]
      , [op FSubL AssocLeft , op FSubR AssocRight
        ,op FImpR AssocRight, op FImpL AssocLeft ]
      , [op FProd AssocRight, op FPlus AssocLeft ]
      ]


structure :: Parsec String () (Term Void)
structure = buildExpressionParser table (parens structure <|> sdia <|> sbox <|> el)
  where
    TokenParser{..} = lexer
    op   c = Infix   (con c >> return (sbin c))
    pre  c = Prefix  (con c >> return (\x -> Con c [x]))
    post c = Postfix (con c >> return (\x -> Con c [x]))
    el     = down <$> between cdot cdot formula
    sdia   = (\x -> Con SDia [x]) <$> angles structure
    sbox   = (\x -> Con SBox [x]) <$>
             (brackets structure <|> between (symbol "⟨") (symbol "⟩") structure)
    cdot   = symbol "." <|> symbol "·"
    table =
      [ [pre S0L , post S0R , pre S1L , post S1R ]
      , [op SSubL AssocLeft , op SSubR AssocRight
        ,op SImpR AssocRight, op SImpL AssocLeft ]
      , [op SProd AssocRight, op SPlus AssocLeft ]
      ]


judgement :: Parsec String () (Term Void)
judgement = do

  let TokenParser{..} = P.makeTokenParser lexerDef

  x <- brackets formula <|> structure
  reservedOp (show (Agda JStruct)) <|> reservedOp (show (ASCII JStruct))
  if isFormula x
    then do y <- structure
            return (Con JFocusL [x,y])
    else do y <- brackets formula <|> structure
            if isFormula y
              then return (Con JFocusR [x,y])
              else return (Con JStruct [x,y])


lexerDef :: LanguageDef st
lexerDef = haskellStyle
  { identLetter     = alphaNum <|> oneOf "_'⁻⁺"
  , opStart         = opLetter lexerDef
  , opLetter        = oneOf "*><+-=|⊗⇐⇒⊕⇚⇛⊢"
  , reservedOpNames = concatMap (\x -> [show (Agda x), show (ASCII x)])
                      [FProd, FImpR, FImpL, FPlus, FSubL, FSubR
                      ,SProd, SImpR, SImpL, SPlus, SSubL, SSubR
                      ,F0L  , F0R  , FBox , F1L  , F1R  , FDia
                      ,JStruct]
  }


lexer :: TokenParser st
lexer = P.makeTokenParser lexerDef
