{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE FunctionalDependencies #-}
module NLQ.Prelude
       (Word,Entry(..),(∷),(<$),($>),lex,lex_,id
       ,S,N,NP,PP,INF,A,IV,TV,QW,QS,NS
       ,Combine(..),nlq,allNLQ,parseBwd,module X) where


import           Prelude hiding (Word,abs,lex,not,(*),($),(<$),($>))
import           Control.Arrow (first)
import           Control.Applicative ((<|>))
import           Control.Monad.State (State,evalState,get,put)
import           Data.Char (isSpace)
import           Data.List (intersperse)
import           Data.Maybe (isJust,fromJust)
import           Data.Singletons.Prelude (SingI(..))
import           NLQ.Syntax.Base            as X hiding (Atom(..))
import qualified NLQ.Syntax.Base            as Syn (Atom(..))
import qualified NLQ.Syntax.Backward        as Bwd
import           NLQ.Semantics              as X
import           NLQ.Semantics.Postulate    as X
import           Text.Parsec (parse,try,many1,between,ParseError)
import           Text.Parsec.Token
import           Text.Parsec.Language (haskellStyle,haskellDef)
import           Text.Parsec.String (Parser)
import           Language.Haskell.TH (lookupValueName,Exp(..),Lit(..))
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote (QuasiQuoter(..))



-- * Synonyms for syntactic types

type S        = El 'Syn.S
type N        = El 'Syn.N
type NP       = El 'Syn.NP
type PP       = El 'Syn.PP
type INF      = El 'Syn.INF
type A        = N  :← N
type IV       = NP :→ S
type TV       = IV :← NP
type QW a b c = QLW ((b :⇦ a) :⇨ c)
type QS a b c = QLS (ImpR (Quan Strong) (ImpL (Quan Strong) b a) c)
type NS       = QS NP S S




-- * Words and "lexical entries"

type Word  a = Entry (StI a)
data Entry x = Entry (SStructI x) (Hask (HI x))

infix 1 ∷

(∷) :: Name -> Univ a -> Hask a
n ∷ a = toHask a (PRIM(Prim a n))

lex_ :: (SingI a) => Hask (H a) -> Word a
lex_ f = Entry (SStI sing) f

lex  :: (SingI a) => Name -> Word a
lex  n = let a = sing in Entry (SStI a) (n ∷ (h a))

instance Show (Entry x) where
  show (Entry x f) = show (fromHask (hi x) f)

(<$) :: Entry (StI (b :← a)) -> Entry (StI a) -> Entry (StI b)
(Entry (SStI (b :%← _)) f) <$ (Entry (SStI _) x) = Entry (SStI b) (f x)

($>) :: Entry (StI a) -> Entry (StI (a :→ b)) -> Entry (StI b)
(Entry (SStI _) x) $> (Entry (SStI (_ :%→ b)) f) = Entry (SStI b) (f x)




-- ** Backward-Chaining Proof Search

data MkDel (k :: Strength) (a :: *) where
  MkDel :: SStrength k -> a -> MkDel k a

class Combine a b | a -> b where
  combine :: a -> b

instance Combine (Entry t) (Entry t) where
  combine = id

instance (Combine x (Entry a)) => Combine (MkDel k x) (Entry (DIA (Del k) a)) where
  combine (MkDel k x) = case combine x of
    (Entry a r) -> Entry (SDIA (SDel k) a) r

instance (Combine x1 (Entry a1), Combine x2 (Entry a2))
         => Combine (x1,x2) (Entry (a1 :∙ a2)) where
  combine (x1,x2) = case (combine x1,combine x2) of
    (Entry x f, Entry y g) -> withHI x (withHI y (Entry (x :%∙ y) (f, g)))




-- * Machinery for printing results

data Meanings t = Meanings String [(Expr t,Expr t)]

instance Show (Meanings t) where
  show (Meanings str terms) =
    concat (intersperse "\n" (map (show.snd) terms))

putMeanings :: Meanings t -> IO ()
putMeanings (Meanings str terms) =
  do putStrLn str; putLength (length terms); putAll [] terms
  where
    putLength 0 = do putStrLn (red "0")
    putLength n = do putStrLn (show n)
    putAll _  [    ] = return ()
    putAll vs ((x,y):xs) = do
      let v = show x
      let w = show y
      putStrLn ((if v `elem` vs then red else green) (v ++ "\n-> " ++ w))
      putAll (v:vs) xs

red   str = "\x1b[31m" ++ str ++ "\x1b[0m"
green str = "\x1b[32m" ++ str ++ "\x1b[0m"

parseBwd :: Combine a (Entry x) => String -> SType b -> a -> Meanings (H b)
parseBwd str b arg = Meanings str (zip terms_HS1 terms_HS2)
  where
    arg1         = evalState (mkArg x) (words (fixWS str))
    Entry x arg2 = combine arg
    terms_NL     = Bwd.findAll (x :%⊢ SStO b)
    terms_HS1    = map (\f -> fromHask (h b) (eta f arg1)) terms_NL
    terms_HS2    = map (\f -> fromHask (h b) (eta f arg2)) terms_NL

    mkArg :: SStructI x -> State [String] (Hask (HI x))
    mkArg (SStI    a  ) = do (n:ns) <- get; put ns; return (n ∷ h a)
    mkArg (SDIA  k x  ) = mkArg x
    mkArg  SB           = return (EXPR())
    mkArg  SC           = return (EXPR())
    mkArg (SUNIT k    ) = return (EXPR())
    mkArg (SPROD k x y) = (,) <$> mkArg x <*> mkArg y


fixWS :: String -> String
fixWS [] = []
fixWS (' ':' ':xs) = fixWS (' ':xs)
fixWS ('(':    xs) = fixWS xs
fixWS (')':    xs) = fixWS xs
fixWS ('<':    xs) = fixWS xs
fixWS ('>':    xs) = fixWS xs
fixWS ( x :    xs) = x : fixWS xs




-- ** QuasiQuoter for backward-chaining proof search

nlq :: QuasiQuoter
nlq = QuasiQuoter
  { quoteExp = nlq, quotePat = undefined, quoteType = undefined, quoteDec = undefined }
  where
    -- generate `parseBwd $(strExp) S $(treeExp)`
    nlq str =
      AppE (AppE (AppE (VarE 'parseBwd) strExp)
            (AppE (ConE 'SEl) (ConE 'SS))) <$> treeExp
      where
      treeExp = case parseTree str of
        Left  err -> fail (show err)
        Right exp -> exp

      strExp = LitE (StringL (fixWS (dropWhile isSpace str)))

allNLQ :: Name -> TH.Q Exp
allNLQ s = do
  list <- go 0
  return (AppE (VarE 'sequence_) (ListE list))
  where
    go :: Int -> TH.Q [Exp]
    go n = do m <- lookupValueName (s ++ show n)
              case m of
                Just x  -> do xs <- go (n + 1)
                              return (AppE (VarE 'putMeanings) (VarE x) : xs)
                Nothing -> return []

parseTree :: String -> Either ParseError (TH.Q Exp)
parseTree = parse (whiteSpace *> pTree1) ""
  where
    TokenParser{whiteSpace,identifier,parens,symbol,angles} = makeTokenParser haskellStyle
    LanguageDef{reservedNames} = haskellDef

    pTree1 :: Parser (TH.Q Exp)
    pTree1 = tuple <$> many1 (pWord <|> (try pDelS <|> pDelW) <|> parens pTree1)
      where
      tuple :: [TH.Q Exp] -> TH.Q Exp
      tuple xs = do xs <- sequence xs
                    return (foldr1 (\x y -> TupE [x,y]) xs)

    pDelW :: Parser (TH.Q Exp)
    pDelW = reset <$> angles pTree1
      where
      reset :: TH.Q Exp -> TH.Q Exp
      reset x = AppE (AppE (ConE 'MkDel) (ConE 'SWeak)) <$> x

    pDelS :: Parser (TH.Q Exp)
    pDelS = reset <$> doubleAngles pTree1
      where
      reset :: TH.Q Exp -> TH.Q Exp
      reset x = AppE (AppE (ConE 'MkDel) (ConE 'SStrong)) <$> x
      doubleAngles p = between (symbol "<<") (symbol ">>") p

    pWord  :: Parser (TH.Q Exp)
    pWord  = do x <- identifier
                let x' = if x `elem` reservedNames then x++"_" else x
                let xn = lookupValueName x'
                    go :: Maybe TH.Name -> TH.Q Exp
                    go (Just xn) = return (VarE xn)
                    go  Nothing  = fail ("unknown name '"++x'++"'")
                return (xn >>= go)

-- -}
-- -}
-- -}
-- -}
-- -}
