{-# LANGUAGE RecordWildCards, RankNTypes, TupleSections #-}
module CG.Parsing (readSystem
                  ,readLexicon
                  ,parseGoal
                  ,formula
                  ,structure
                  ,judgement
                  )where


import           CG.Base
import           Data.Char (isSpace)
import           Data.List (nub,isPrefixOf)
import           Data.Void (Void)
import           Data.Map (Map)
import qualified Data.Map as M
import           Text.Parsec hiding (option)
import           Text.Parsec.Expr
import           Text.Parsec.Error (setErrorPos)
import           Text.Parsec.String (Parser)
import           Text.Parsec.Language (LanguageDef,haskellStyle)
import           Text.Parsec.Token (TokenParser,GenTokenParser(..),GenLanguageDef(..),makeTokenParser)
import           System.Directory (doesFileExist)
import           System.Environment (getEnv)
import           System.FilePath ((</>))


-- * Variable Parsing

class VarParser v where
  formulaVar   :: Parser v
  structureVar :: Parser v

instance VarParser Void where
  formulaVar   = oneOf "ABCD" *> unexpected "Variables {A,B,C,D} are not allowed."
  structureVar = oneOf "XYZW" *> unexpected "Variables {X,Y,Z,W} are not allowed."

instance VarParser Char where
  formulaVar   = lexeme cg (oneOf "ABCD") <?> "formula variable"
  structureVar = lexeme cg (oneOf "XYZW") <?> "structure variable"


-- * Language Definition

cgDef :: LanguageDef st
cgDef = haskellStyle
  { identStart    = identLetter cgDef
  , identLetter   = satisfy (\c -> not (isSpace c || c `elem` "()"))
  , opStart       = opLetter cgDef
  , opLetter      = oneOf "()"
  , reservedNames = let

    reservedNames   = ["where","and","atomic","positive","negative"]
    reservedOpNames = nub (map toString operators ++ map (toString . ASCII) operators)
    operators       = concat [unaryLogical ,unaryStructural
                             ,binaryLogical,binaryStructural
                             ,sequents, [Down]]

    in reservedNames ++ reservedOpNames
  }

cg :: TokenParser st
cg = makeTokenParser cgDef


-- * Term Parsing

con :: ConId -> Parser ()
con c = reserved (toString c) <|> reserved (toString (ASCII c))
  where
    TokenParser{..} = cg

con' :: ConId -> Parser ()
con' c = do symbol (toString c) <|> symbol (toString (ASCII c)); return ()
  where
    TokenParser{..} = cg

infl c = Infix   (con c *> return (binary c)) AssocLeft
infr c = Infix   (con c *> return (binary c)) AssocRight
pref c = Prefix  (con c *> return (unary  c))
post c = Postfix (con c *> return (unary  c))


atom :: Parser (Term ConId v)
atom = do
  let TokenParser{..} = cg
  x <- identifier
  return . nullary $
    if last x `elem` "⁻'"
      then NegAtom (init x)
      else PosAtom       x


formulaWithVar :: Parser (Term ConId Char)
formulaWithVar = formula

formula :: VarParser v => Parser (Term ConId v)
formula =
  buildExpressionParser table (parens formula <|> fvar <|> atom)
  where
    TokenParser{..} = cg
    fvar  = Var <$> formulaVar
    table =
      [ [ pref F0L   , post F0R   , pref FBox
        , pref F1L   , post F1R   , pref FDia  ]
      , [ infl FSubL , infl FImpL , infl HImpL
        , infr FSubR , infr FImpR , infr HImpR ]
      , [ infr FProd , infl FPlus , infr HProd ]
      ]


structureWithVar :: Parser (Term ConId Char)
structureWithVar = structure

structure :: VarParser v => Parser (Term ConId v)
structure =
  buildExpressionParser table (parens structure <|> sdia <|> sbox <|> svar <|> down)
  where
    TokenParser{..} = cg

    svar    = Var <$> structureVar
    down    = unary Down <$> cdots formula <?> "down operator"
    sdia    = unary SDia <$> (angles structure <|> rangles structure)
    sbox    = unary SBox <$> (brackets structure)
    cdots   = between (con Down)   (con Down)
    rangles = between (symbol "⟨") (symbol "⟩")
    table   =
      [ [ pref S0L   , post S0R   , pref S1L   , post S1R   ]
      , [ infl SSubL , infl SImpL , infr SSubR , infr SImpR ]
      , [ infr SProd , infl SPlus ]
      , [ infr Comma ]
      ]


judgementWithVar :: Parser (Term ConId Char)
judgementWithVar = judgement

judgement :: VarParser v => Parser (Term ConId v)
judgement =
  spaces *> (try (try jstruct <|> (try jfocusl <|> jfocusr)) <|> jalgebr)
  where
    TokenParser{..} = cg

    jstruct = binary JStruct <$> structure        <* con' JStruct <*> structure
    jfocusl = binary JFocusL <$> brackets formula <* con' JFocusL <*> structure
    jfocusr = binary JFocusR <$> structure        <* con' JFocusL <*> brackets formula
    jalgebr = binary JAlgebr <$> formula          <* con' JAlgebr <*> formula


lexicon :: Parser (Map String (Term ConId Void))
lexicon = M.fromList <$> many1 entry
  where
    TokenParser{..} = cg
    entry = (,) <$> identifier <* symbol ":" <*> formula


guard' :: Parser (Term ConId Char -> Guard ConId)
guard' =
  do reserved "where"
     gs <- sepBy1 single (reserved "and")
     if null gs
       then unexpected "panic!"
       else return (foldr1 and gs)
  where
    TokenParser{..} = cg
    and f g x = f x `And` g x
    single    = predicate <*> formulaVar
    predicate = choice
      [ reserved "atomic"   *> return atomic
      , reserved "positive" *> return positive
      , reserved "negative" *> return negative
      ]


rule :: Parser (Rule ConId Int)
rule = do
  n  <- identifier
  _  <- symbol ":"
  js <- sepBy1 judgement sep

  let ps   = init js
  let c    = last js
  let rule = mkRule n ps c

  mb <- optionMaybe guard'
  return $
    case mb of
     Just mk -> rule { guard = mk c }
     _       -> rule

  where
    TokenParser{..} = cg
    sep = symbol "→" <|> symbol "-->"


option :: Parser Option
option = do
  symbol "set"
  choice (map try
    [ symbol "finite"      *> return (IsFinite True)
    , symbol "infinite"    *> return (IsFinite False)
    , symbol "algebraic"   *> return (IsStructural False)
    , symbol "structural"  *> return (IsStructural True)
    , symbol "agda_name"   *> symbol "=" *> (AgdaName   <$> many1 (satisfy (not . isSpace)))
    , symbol "agda_module" *> symbol "=" *> (AgdaModule <$> many1 (satisfy (not . isSpace)))
    , symbol "parse_with"  *> symbol "=" *> (ParseWith  <$> pParseWith)
    ])
    <?> "option"
    where
      TokenParser{..} = cg
      pParseWith :: Parser [ParseWith]
      pParseWith = many1 (useBinary <|> useUnary)
        where
          useOp opt = choice . map (\c -> con c >> return (opt c))
          useUnary  = useOp UseUnary  (unaryLogical  ++ unaryStructural)
          useBinary = useOp UseBinary (binaryLogical ++ binaryStructural)


-- * Options

data Option
  = IsFinite Bool
  | IsStructural Bool
  | ParseWith [ParseWith]
  | AgdaName String
  | AgdaModule String
  deriving Show

data ParseWith
  = UseUnary ConId
  | UseBinary ConId
  deriving Show


-- |Handle options for proof systems.
runOptions :: [Option] -> System ConId
runOptions = postProcess . foldr runOption emptySystem
  where
    runOption (IsFinite     b) s = s { finite     = b }
    runOption (IsStructural b) s = s { structural = b }
    runOption (AgdaName     n) s = s { agdaName   = Just n }
    runOption (AgdaModule   n) s = s { agdaModule = Just n }
    runOption (ParseWith    x) s = foldr runPW s x

    runPW (UseUnary  op) = addUnary  op
    runPW (UseBinary op) = addBinary op

    postProcess sys@System{..}
      | structural = sys { unaryOp  = fmap toStructural unaryOp
                         , binaryOp = fmap toStructural binaryOp }
      | otherwise  = sys


-- * Parsers

parseGoal :: String -> IO (Term ConId Void)
parseGoal str = case parse formula "" str of
  Left  e -> fail ("Could not parse goal formula `"++show str++"'.\n"++show e)
  Right x -> return x

readLexicon :: FilePath -> IO (Map String (Term ConId Void))
readLexicon lexiconFile = do
  fileExist <- doesFileExist lexiconFile
  if fileExist
    then unsafeReadLexicon lexiconFile
    else do cgtoolHome <- getEnv "CGTOOL_HOME"
            let lexiconFile' = cgtoolHome </> "lex" </> lexiconFile
            fileExist' <- doesFileExist lexiconFile'
            if fileExist'
              then unsafeReadLexicon lexiconFile'
              else error ("no such file: " ++ lexiconFile)

unsafeReadLexicon :: FilePath -> IO (Map String (Term ConId Void))
unsafeReadLexicon lexiconFile = do
  lexiconContent <- readFile lexiconFile
  case parse lexicon lexiconFile lexiconContent of
   Left  e -> fail ("Could not parse lexicon.\n"++show e)
   Right l -> return l

readSystem :: FilePath -> IO (System ConId)
readSystem systemFile = do
  fileExist <- doesFileExist systemFile
  if fileExist
    then unsafeReadSystem systemFile
    else do cgtoolHome <- getEnv "CGTOOL_HOME"
            let systemFile' = cgtoolHome </> "sys" </> systemFile
            fileExist' <- doesFileExist systemFile'
            if fileExist'
              then unsafeReadSystem systemFile'
              else error ("no such file: " ++ systemFile)

unsafeReadSystem :: FilePath -> IO (System ConId)
unsafeReadSystem systemFile = go <$> readFile systemFile
  where
    go contents = sys { rules = rules }
      where
        TokenParser{..} = cg

        (rawOpts,rawRules)
          = span (isOption . snd)            -- break at first non-option
            $ filter (not . isComment . snd) -- filter out all comments
            $ zip [1..]                      -- add line numbers
            $ lines contents                 -- split lines

        opts  = map (parseOrError option systemFile) rawOpts
        rules = map (parseOrError rule   systemFile) rawRules
        sys   = runOptions opts

        isOption  ln = "set" `isPrefixOf` ln
        isComment ln = case parse (whiteSpace *> eof) "" ln of
          Left  _ -> False
          Right _ -> True

    parseOrError :: Parser a -> FilePath -> (Line, String) -> a
    parseOrError p fn (n,str) = case parse p fn str of
      Left  e -> error (show (setErrorPos (setSourceLine (errorPos e) n) e))
      Right x -> x
