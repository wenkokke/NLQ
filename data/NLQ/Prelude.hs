{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE ImplicitParams         #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
module NLQ.Prelude
       (Word,Entry(..),(∷),(<$),($>),lex,lex_,id
       ,S,N,NP,PP,INF,A,IV,TV,Q,NS
       ,Boolean(..)
       ,Combine(..),nlq,nlqAll,parseBwd,module X) where


import           Prelude hiding (Word,abs,lex,not,(*),($),(<$),($>))
import           Control.Arrow (first)
import           Control.Applicative ((<|>))
import           Control.Monad (when)
import           Control.Monad.State (State,evalState,get,put)
import           Data.Char (isSpace)
import           Data.List (intersperse)
import           Data.Maybe (isJust,fromJust)
import           Data.Proxy (Proxy(..))
import           Data.Singletons.Decide ((:~:)(..))
import           Data.Singletons.Prelude (SingI(..))
import           Data.Singletons.Prelude.List ((:++))
import qualified Data.Singletons.Prelude.List as SL
import           NLQ.Syntax.Base            as X hiding (Q,Atom(..))
import qualified NLQ.Syntax.Base            as Syn (Atom(..))
import qualified NLQ.Syntax.Backward        as Bwd
import qualified NLQ.Syntax.Forward         as Fwd
import           NLQ.Semantics              as X
import           NLQ.Semantics.Postulate    as X
import           Text.Parsec (parse,many1,ParseError)
import           Text.Parsec.Token
import           Text.Parsec.Language (haskellStyle,haskellDef)
import           Text.Parsec.String (Parser)
import           Language.Haskell.TH (lookupValueName,Exp(..),Lit(..))
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH.Quote (QuasiQuoter(..))


type S       = El 'Syn.S
type N       = El 'Syn.N
type NP      = El 'Syn.NP
type PP      = El 'Syn.PP
type INF     = El 'Syn.INF
type A       = N  :← N
type IV      = NP :→ S
type TV      = IV :← NP
type Q a b c = UnitR KHol (c :⇦ (a :⇨ b))
type NS      = Q NP S S


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


-- * Boolean types, and generalised `past tense` modifier

class Boolean a where
  past :: UnivI a => Hask a -> Hask a
  past (x :: Hask a) = past_ (univ :: Univ a) x
  past_ :: Univ  a -> Hask a -> Hask a

instance Boolean T where
  past_ T = "past" ∷ TT

instance (Boolean b) => Boolean (a -> b) where
  past_ (a :-> b) f x = past_ b (f x)


-- ** Backward-Chaining Proof Search

class Combine a b | a -> b where
  combine :: a -> b

instance Combine (Entry t) (Entry t) where
  combine = id

instance (Combine x (Entry a)) => Combine [x] (Entry (DIA KRes a)) where
  combine [x] = case combine x of
    (Entry a r) -> Entry (SDIA SKRes a) r

instance (Combine x1 (Entry a1), Combine x2 (Entry a2))
         => Combine (x1,x2) (Entry (a1 :∙ a2)) where
  combine (x1,x2) = case (combine x1,combine x2) of
    (Entry x f, Entry y g) -> withHI x (withHI y (Entry (x :%∙ y) (f, g)))


-- ** Type and DSL for lexicon entries

data Meanings t = Meanings String [(Expr t,Expr t)]


instance Show (Meanings t) where
  show (Meanings str terms) =
    concat (intersperse "\n" (map show terms))


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


-- ** QuasiQuoter for Backward-Chaining Proof Search

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

nlqAll :: Name -> TH.Q Exp
nlqAll s = do
  list <- go 0
  return (AppE (VarE 'sequence_) (ListE list))
  where
    go :: Int -> TH.Q [Exp]
    go n = do m <- lookupValueName (s ++ show n)
              case m of
                Just x  -> do xs <- go (n + 1)
                              return (AppE (VarE 'putMeanings) (VarE x) : xs)
                Nothing -> return []

-- n = do
--   bwds1 <- traverse lookupValueName (map (("s"++).show) [0..n])
--   let bwds2 = map (VarE . fromJust) (takeWhile isJust bwds1)
--   return (AppE (AppE (VarE 'mapM_) (VarE 'putResult)) (ListE bwds2))

parseTree :: String -> Either ParseError (TH.Q Exp)
parseTree = parse (whiteSpace *> pTree1) ""
  where
    TokenParser{whiteSpace,identifier,parens,angles} = makeTokenParser haskellStyle
    LanguageDef{reservedNames} = haskellDef

    pTree1 :: Parser (TH.Q Exp)
    pTree1 = tuple <$> many1 (pWord <|> pReset <|> parens pTree1)
      where
      tuple :: [TH.Q Exp] -> TH.Q Exp
      tuple xs = do xs <- sequence xs
                    return (foldr1 (\x y -> TupE [x,y]) xs)

    pReset :: Parser (TH.Q Exp)
    pReset = reset <$> angles pTree1
      where
      reset :: TH.Q Exp -> TH.Q Exp
      reset x = ListE . (:[]) <$> x

    pWord  :: Parser (TH.Q Exp)
    pWord  = do x <- identifier
                let x' = if x `elem` reservedNames then x++"_" else x
                let xn = lookupValueName x'
                    go :: Maybe TH.Name -> TH.Q Exp
                    go (Just xn) = return (VarE xn)
                    go  Nothing  = fail ("unknown name '"++x'++"'")
                return (xn >>= go)


-- ** Forward-Chaining Proof Search (Experimental)
{-
parseFwd :: SType b -> Entries xs ->  IO ()
parseFwd (b :: SType b) (xs :: Entries xs) = do
  let
    prfs1 :: [Fwd.TypedBy xs b]
    prfs1 = Fwd.findAll (typeofs xs) b
    prfs2 :: [String]
    prfs2 = map go prfs1

    go (Fwd.TypedBy x Refl f) =
      case joinTree x xs of
      Entry _ g -> show (runHask (abs (eta (x :%⊢ SStO b) f)) (Cons g Nil))

  print (length prfs2)
  mapM_ putStrLn prfs2

infixr 4 ∷; (∷) = SCons; (·) = SNil

data Entries (xs :: [StructI]) where
  SNil  :: Entries '[]
  SCons :: Entry x -> Entries xs -> Entries (x ': xs)

typeofs :: Entries xs -> SL.SList xs
typeofs  SNil                  = SL.SNil
typeofs (SCons (Entry x _) xs) = SL.SCons x (typeofs xs)

joinTree :: SStructI x -> Entries (ToList x) -> Entry x
joinTree (SStI a) (SCons x SNil) = x
joinTree (SDIA k x) env = entryDIA k (joinTree x env)
  where
    entryDIA :: SKind k -> Entry x -> Entry (DIA k x)
    entryDIA k (Entry x r) = Entry (SDIA k x) r
joinTree (SPROD k x y) env = entryPROD k (joinTree x xs) (joinTree y ys)
  where
    (xs,ys) = sBreak (fromJust (sToList x)) env
    sBreak :: SL.SList xs -> Entries (xs :++ ys) -> (Entries xs, Entries ys)
    sBreak  SL.SNil                 env  = (SNil, env)
    sBreak (SL.SCons _ xs) (SCons x env) = first (SCons x) (sBreak xs env)
    entryPROD :: SKind k -> Entry x -> Entry y -> Entry (PROD k x y)
    entryPROD k (Entry x f) (Entry y g)  =
      Entry (SPROD k x y) (withHI x (withHI y (pair(f,g))))

-- -}
-- -}
-- -}
-- -}
-- -}
