{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module NLIBC.Base
       (Entry(..),(-:),(~:),(<$),($>)
       ,prim,not,lam,pair,forall,exists
       ,module X,S,N,NP,PP,INF,IV,TV,Q,NS
       ,(*),parseBwd) where


import           Prelude hiding (not,(*),($),(<$),($>))
import           NLIBC.Syntax.Base     as X hiding (Q,Atom(..))
import qualified NLIBC.Syntax.Base     as Syn (Atom(..))
import qualified NLIBC.Syntax.Backward as Bwd
import           NLIBC.Semantics       as X hiding (Sem(pair))
import qualified NLIBC.Semantics       as Sem



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


-- * Type and DSL for lexicon entries

prim :: Univ t -> Name -> Expr t
prim t n = PRIM(Prim t n)

not :: Expr T -> Expr T
not x = Not x

lam :: (UnivI a, UnivI b) => EXPR (a -> b) -> Expr (a -> b)
lam = EXPR

pair :: (UnivI a, UnivI b) => EXPR (a , b) -> Expr (a , b)
pair = EXPR

exists :: UnivI t => Univ t -> EXPR (t -> T) -> Expr T
exists t x = Exists t x

forall :: UnivI t => Univ t -> EXPR (t -> T) -> Expr T
forall t x = ForAll t x

data Entry x = Entry (SStructI x) (Expr (HI x))

infix 1 -:, ~:

(-:) :: Expr (H t) -> SType t -> Entry (StI t)
x -: t = Entry (SStI t) x

(~:) :: Name -> SType t -> Entry (StI t)
n ~: t = Entry (SStI t) (PRIM (Prim (h t) n))

instance Show (Entry t) where
  show (Entry _ f) = show f

(<$) :: Entry (StI (b :← a)) -> Entry (StI a) -> Entry (StI b)
(Entry (SStI (b :%← _)) f) <$ (Entry (SStI _) x) = Entry (SStI b) (f $ x)

($>) :: Entry (StI a) -> Entry (StI (a :→ b)) -> Entry (StI b)
(Entry (SStI _) x) $> (Entry (SStI (_ :%→ b)) f) = Entry (SStI b) (f $ x)


-- ** Combining entries in trees

infixr 3 *; (*) = (,)

class Combine a b | a -> b where
  combine :: a -> b

instance Combine (Entry t) (Entry t) where
  combine = id

instance (Combine x (Entry a)) => Combine [x] (Entry (DIA KRes a)) where
  combine [x] = case combine x of (Entry a r) -> Entry (SDIA SKRes a) r

instance (Combine x1 (Entry a1), Combine x2 (Entry a2))
         => Combine (x1,x2) (Entry (a1 :∙ a2)) where
  combine (x1,x2) = case (combine x1,combine x2) of
    (Entry x f, Entry y g) -> withHI x (withHI y (Entry (x :%∙ y) (EXPR (f, g))))


parseBwd :: Combine x (Entry a) => SType b -> x -> IO ()
parseBwd b e = do
  let
    (Entry x r) = combine e
    synSeq      = x :%⊢ SStO b
    synPrfs     = Bwd.findAll synSeq
    semPrfs     = ($ r) . flip runHask Nil . eta synSeq <$> synPrfs
  print (length synPrfs)
  mapM_ print  semPrfs

-- -}
-- -}
-- -}
-- -}
-- -}
