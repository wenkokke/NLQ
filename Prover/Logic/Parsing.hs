{-# LANGUAGE RecordWildCards #-}
module Logic.Parsing where


import           Data.List (nub)
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
import           Logic.Printing (Agda(..),ASCII(..),BS(..))


-- * Parsing formulas

atom :: Parsec String () (Term v)
atom = (nullary . Atom) <$> identifier <?> "atomic formulas"
  where
    TokenParser{..} = lexer


void :: Parsec String () Void
void = unexpected "Variables A,B,C,D and X,Y,Z,W are not allowed."


nullary :: ConId -> Term v
nullary c = Con c []

unary   :: ConId -> Term v -> Term v
unary   c x = Con c [x]

binary  :: ConId -> Term v -> Term v -> Term v
binary  c x y = Con c [x,y]


con :: ConId -> Parsec String () ()
con c = reservedOp (show (Agda c))
        <|> reservedOp (show (ASCII c))
        <|> reservedOp (show (BS c))
  where TokenParser{..} = lexer


lexicon :: Parsec String () (Map String (Term Void))
lexicon = M.fromList <$> many1 entry
  where
    TokenParser{..} = lexer
    entry = (,) <$> identifier <* symbol ":" <*> formula void


formula :: (IsVar v) => Parsec String () v -> Parsec String () (Term v)
formula fv = buildExpressionParser table
           $ parens (formula fv) <|> (Var <$> fv) <|> atom
  where
    TokenParser{..} = lexer
    op   c = Infix   (con c >> return (binary c))
    pre  c = Prefix  (con c >> return (unary c))
    post c = Postfix (con c >> return (unary c))


    table =
      [ [pre F0L , post F0R , pre F1L , post F1R
        ,pre FBox           , pre FDia           ]
      , [op FSubL AssocLeft , op FSubR AssocRight
        ,op FImpR AssocRight, op FImpL AssocLeft ]
      , [op FProd AssocRight, op FPlus AssocLeft ]
      ]


structure :: (IsVar v) => Parsec String () v -> Parsec String () v -> Parsec String () (Term v)
structure fv sv = buildExpressionParser table
                $ parens (structure fv sv) <|> sdia <|> sbox <|> (Var <$> sv) <|> form
  where
    TokenParser{..} = lexer
    op   c = Infix   (con c >> return (binary c))
    pre  c = Prefix  (con c >> return (unary c))
    post c = Postfix (con c >> return (unary c))

    form   = unary Down <$> between cdot cdot (formula fv)
    sdia   = unary SDia <$> (angles (structure fv sv) <|> between ropen rclose (structure fv sv))
    sbox   = unary SBox <$> brackets (structure fv sv)

    cdot   = symbol "." <|> symbol "·"
    ropen  = symbol "⟨"
    rclose = symbol "⟩"

    table  =
      [ [pre S0L , post S0R , pre S1L , post S1R ]
      , [op SSubL AssocLeft , op SSubR AssocRight
        ,op SImpR AssocRight, op SImpL AssocLeft ]
      , [op SProd AssocRight, op SPlus AssocLeft ]
      ]


judgementVar :: Parsec String () (Term String)
judgementVar = judgement formulaVar structureVar

judgement :: (IsVar v) => Parsec String () v -> Parsec String () v -> Parsec String () (Term v)
judgement fv sv = spaces *> (try (try jstruct <|> (try jfocusl <|> jfocusr)) <|> jform)
  where
    TokenParser{..} = lexer
    form   = formula   fv
    struct = structure fv sv

    jstruct = binary JStruct <$> struct        <* con JStruct <*> struct
    jfocusl = binary JFocusL <$> brackets form <* con JFocusL <*> struct
    jfocusr = binary JFocusR <$> struct        <* con JFocusL <*> brackets form
    jform   = binary JForm   <$> form          <* con JForm   <*> form


lexerDef :: LanguageDef st
lexerDef = haskellStyle
  { identLetter     = alphaNum <|> oneOf "_'⁻⁺"
  , opStart         = opLetter lexerDef
  , opLetter        = oneOf "*><+-=|⊗⇐⇒⊕⇚⇛⊢∙∘"
  , reservedOpNames = nub $ concatMap (\x -> [show (Agda x), show (ASCII x), show (BS x)])
                      [FProd, FImpR, FImpL, FPlus, FSubL, FSubR
                      ,SProd, SImpR, SImpL, SPlus, SSubL, SSubR
                      ,F0L  , F0R  , FBox , F1L  , F1R  , FDia
                      ,JStruct]
  }


lexer :: TokenParser st
lexer = P.makeTokenParser lexerDef


-- TODO: passing these parsers as arguments along the tree is a bit
--       of an ugly solution; perhaps I should restructure the code
formulaVar :: Parsec String () String
formulaVar = lexeme lexer ((:[]) <$> oneOf "ABCD")

structureVar :: Parsec String () String
structureVar = lexeme lexer ((:[]) <$> oneOf "XYZW")


-- TODO: defining this operator here feels a bit out of place, even
--       though this is the earliest position where it can be defined
--       perhaps I should move it to `Rules.hs'
infixr 1 ⟶

(⟶) :: [String] -> String -> RuleId -> Rule ConId Int
(⟶) ps c n = let j = judgement formulaVar structureVar in
    case mapM (parse j "Rules.hs") ps of
     Left err  -> error ("Cannot parse premises of rule `"++n++"' in `Rules.hs'.\n"++show err)
     Right ps' ->
       case parse j "Rules.hs" c of
        Left err -> error ("Cannot parse conclusion of rule `"++n++"' in `Rules.hs'.\n"++show err)
        Right c' -> mkRule ps' c' n
