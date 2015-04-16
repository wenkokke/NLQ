{-# LANGUAGE RecordWildCards #-}
module Logic.Parsing (lexicon,judgement,judgementVar,structure,structureVar,formula,formulaVar)where


import           Data.List (nub)
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Void (Void)
import           Text.Parsec hiding (getInput)
import           Text.Parsec.Expr
import           Text.Parsec.Language (LanguageDef,haskellStyle)
import           Text.Parsec.Token (TokenParser,GenTokenParser(..),GenLanguageDef(..))
import qualified Text.Parsec.Token as P

import           Logic.Base
import           Logic.Printing (Agda(..),ASCII(..))


-- * Export-ready parsers


-- |Parse a formula using (A,B,C,D) as variables.
formulaVar   :: Parsec String () (Term String)
formulaVar   = formula' varForFormula

-- |Parse a formula without variables.
formula      :: Parsec String () (Term Void)
formula      = formula' void

-- |Parse a structure using (A,B,C,D) and (X,Y,Z,W) as variables.
structureVar :: Parsec String () (Term String)
structureVar = structure' varForFormula varForStructure

-- |Parse a structure without variables.
structure    :: Parsec String () (Term Void)
structure    = structure' void void

-- |Parse a judgement using (A,B,C,D) and (X,Y,Z,W) as variables.
judgementVar :: Parsec String () (Term String)
judgementVar = judgement' varForFormula varForStructure

-- |Parse a judgement without variables.
judgement    :: Parsec String () (Term Void)
judgement    = judgement' void void



-- * Parsing formulas

void :: Parsec String () Void
void = unexpected "Variables A,B,C,D and X,Y,Z,W are not allowed."


con :: ConId -> Parsec String () ()
con c = reservedOp (show (Agda c)) <|> reservedOp (show (ASCII c))
  where TokenParser{..} = lexer


lexicon :: Parsec String () (Map String (Term Void))
lexicon = M.fromList <$> many1 entry

entry :: Parsec String () (String, Term Void)
entry = (,) <$> identifier <* symbol ":" <*> formula
  where
    TokenParser{..} = lexer


formula' :: (IsVar v) => Parsec String () v -> Parsec String () (Term v)
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


structure' :: (IsVar v) => Parsec String () v -> Parsec String () v -> Parsec String () (Term v)
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
      ]


judgement' :: (IsVar v) => Parsec String () v -> Parsec String () v -> Parsec String () (Term v)
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
  { identLetter     = alphaNum <|> oneOf "_'⁻⁺"
  , opStart         = opLetter lexerDef
  , opLetter        = oneOf "*><+-~=|⊗⇐⇒⊕⇚⇛⊢∘⇨⇦"
  , reservedOpNames = nub $ concatMap (\x -> [show (Agda x), show (ASCII x)])
                      [FProd, FImpR, FImpL, FPlus, FSubL, FSubR
                      ,SProd, SImpR, SImpL, SPlus, SSubL, SSubR
                      ,HProd, HImpR, HImpL
                      ,F0L  , F0R  , FBox , F1L  , F1R  , FDia
                      ,JForm, JStruct, JFocusL, JFocusR]
  }


lexer :: TokenParser st
lexer = P.makeTokenParser lexerDef


varForFormula :: Parsec String () String
varForFormula = lexeme lexer ((:[]) <$> oneOf "ABCD")

varForStructure :: Parsec String () String
varForStructure = lexeme lexer ((:[]) <$> oneOf "XYZW")
