{-# LANGUAGE RecordWildCards, RankNTypes #-}
module CG.Parsing (lexicon,judgement,judgementVar,structure,structureVar,formula,formulaVar)where


import           Data.Char (isSpace)
import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Void (Void)
import           Text.Parsec hiding (getInput)
import           Text.Parsec.Combinator (sepBy1)
import           Text.Parsec.Expr
import           Text.Parsec.String (Parser)
import           Text.Parsec.Language (LanguageDef,haskellStyle)
import           Text.Parsec.Token (TokenParser,GenTokenParser(..),GenLanguageDef(..))
import qualified Text.Parsec.Token as P

import           CG.Base
import           CG.Printing (Agda(..),ASCII(..))


-- * Export-ready parsers

-- |Parse a formula without variables.
formula      :: Parser (Term Void)
formula      = formula' void

-- |Parse a structure without variables.
structure    :: Parser (Term Void)
structure    = structure' void void

-- |Parse a judgement without variables.
judgement    :: Parser (Term Void)
judgement    = judgement' void void

-- |Parse a formula using (A,B,C,D) as variables.
formulaVar   :: Parser (Term String)
formulaVar   = formula' varForFormula

-- |Parse a structure using (A,B,C,D) and (X,Y,Z,W) as variables.
structureVar :: Parser (Term String)
structureVar = structure' varForFormula varForStructure

-- |Parse a judgement using (A,B,C,D) and (X,Y,Z,W) as variables.
judgementVar :: Parser (Term String)
judgementVar = judgement' varForFormula varForStructure


lexicon :: Parser (Map String (Term Void))
lexicon = M.fromList <$> many1 entry
  where
    entry :: Parser (String, Term Void)
    entry = (,) <$> identifier <* symbol ":" <*> formula
      where
        TokenParser{..} = lexer


rule :: Parser (Rule ConId Int)
rule = do
  n  <- ruleName
  _  <- colon
  js <- sepBy1 judgementVar ruleSep
  let ps   = init js
  let c    = last js
  let rule = mkRule ps c n
  mb <- optionMaybe guards
  return $ case mb of
   Just mkG -> rule { guard = runGuard (mkG c) }
   _        -> rule
  where
    TokenParser{..} = lexer
    ruleName = lexeme (many1 (satisfy (not . isSpace))) <?> "Rule Name"
    ruleSep  = symbol "→" <|> symbol "-->"

newtype Guard = Guard { runGuard :: forall v. Term v -> Bool }

guards :: Parser (Term String -> Guard)
guards = do lexeme (string "where")
            gs <- sepBy1 guard' (lexeme (string "and"))
            return (foldr1 gplus gs)
  where
    TokenParser{..} = lexer

    gplus :: (Term String -> Guard) -> (Term String -> Guard) -> Term String -> Guard
    gplus f g c = Guard (\x -> runGuard (f c) x && runGuard (g c) x)

    guard' :: Parser (Term String -> Guard)
    guard' = do p <- pred; k <- varForFormula; return (\c -> mkG p k c)
      where
        pred :: Parser Guard
        pred = choice . map (\(n,g) -> lexeme (string n) *> return g) $
               [ ("atomic"   , Guard isAtomic)
               , ("positive" , Guard isPositive)
               , ("negative" , Guard isNegative)
               ]

        mkG :: Guard -> String -> Term String -> Guard
        mkG p _ (Var i) = Guard mkG' where
          mkG' :: forall v'. Term v' -> Bool
          mkG' (Var _) = True
          mkG'      y  = runGuard p y
        mkG p k (Con x xs) = Guard mkG' where
          mkG' :: forall v'. Term v' -> Bool
          mkG' (Var _)             = True
          mkG' (Con y ys) | x == y = and (zipWith (runGuard . mkG p k) xs ys)
          mkG' _                   = False



-- * Parsers

void :: Parser Void
void = unexpected "Variables A,B,C,D and X,Y,Z,W are not allowed."


con :: ConId -> Parser ()
con c = reservedOp (show (Agda c)) <|> reservedOp (show (ASCII c))
  where
    TokenParser{..} = lexer


formula' :: (IsVar v) => Parser v -> Parser (Term v)
formula' fv =
  buildExpressionParser table (parens form <|> (Var <$> fv) <|> atom)
  where
    TokenParser{..} = lexer
    form   = formula' fv                     <?> "formula"
    atom   = (nullary . Atom) <$> identifier

    op   c = Infix   (con c >> return (binary c))
    pre  c = Prefix  (con c >> return (unary c))
    post c = Postfix (con c >> return (unary c))

    table =
      [ [pre F0L , post F0R , pre F1L , post F1R
        ,pre FBox           , pre FDia           ]
      , [op FSubL AssocLeft , op FSubR AssocRight
        ,op FImpR AssocRight, op FImpL AssocLeft
        ,op HImpR AssocRight, op HImpL AssocLeft ]
      , [op FProd AssocRight, op FPlus AssocLeft
        ,op HProd AssocRight                     ]
      ]


structure' :: (IsVar v) => Parser v -> Parser v -> Parser (Term v)
structure' fv sv =
  buildExpressionParser table (parens struct <|> sdia <|> sbox <|> var <|> form)
  where
    TokenParser{..} = lexer
    struct = structure' fv sv                               <?> "structure"
    form   = unary Down <$> between cdot cdot (formula' fv) <?> "formula"
    var    = Var <$> sv                                     <?> "variable"

    op   c = Infix   (con c >> return (binary c))
    pre  c = Prefix  (con c >> return (unary c))
    post c = Postfix (con c >> return (unary c))

    sdia   = unary SDia <$> (angles struct <|> between ropen rclose struct)
    sbox   = unary SBox <$> brackets struct

    cdot   = symbol "." <|> symbol "·"
    ropen  = symbol "⟨"
    rclose = symbol "⟩"

    table  =
      [ [pre S0L , post S0R , pre S1L , post S1R ]
      , [op SSubL AssocLeft , op SSubR AssocRight
        ,op SImpR AssocRight, op SImpL AssocLeft ]
      , [op SProd AssocRight, op SPlus AssocLeft ]
      , [op Comma AssocRight]
      ]


judgement' :: (IsVar v) => Parser v -> Parser v -> Parser (Term v)
judgement' fv sv =
  spaces *> (try (try jstruct <|> (try jfocusl <|> jfocusr)) <|> jform)
  where
    TokenParser{..} = lexer
    form   = formula'   fv
    struct = structure' fv sv

    jstruct = binary JStruct <$> struct        <* con JStruct <*> struct
    jfocusl = binary JFocusL <$> brackets form <* con JFocusL <*> struct
    jfocusr = binary JFocusR <$> struct        <* con JFocusL <*> brackets form
    jform   = binary JForm   <$> form          <* con JForm   <*> form


lexerDef :: LanguageDef st
lexerDef = haskellStyle
  { identStart      = letter <|> oneOf "⊥"
  , identLetter     = alphaNum <|> oneOf "_'⁻⁺⊥"
  , opStart         = opLetter lexerDef
  , opLetter        = oneOf "*><+-~=|⊗⇐⇒⊕⇚⇛⊢∘⇨⇦,"
  , reservedOpNames = nub $ concatMap (\x -> [show (Agda x), show (ASCII x)])
                      [FProd, FImpR, FImpL, FPlus, FSubL, FSubR
                      ,SProd, SImpR, SImpL, SPlus, SSubL, SSubR
                      ,Comma
                      ,HProd, HImpR, HImpL
                      ,F0L  , F0R  , FBox , F1L  , F1R  , FDia
                      ,JForm, JStruct, JFocusL, JFocusR]
  }


lexer :: TokenParser st
lexer = P.makeTokenParser lexerDef


varForFormula :: Parser String
varForFormula = lexeme lexer ((:[]) <$> oneOf "ABCD")

varForStructure :: Parser String
varForStructure = lexeme lexer ((:[]) <$> oneOf "XYZW")
