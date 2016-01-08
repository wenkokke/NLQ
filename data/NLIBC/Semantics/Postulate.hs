{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
module NLIBC.Semantics.Postulate where


import           Prelude hiding (($),(!!),fst,snd,abs,lookup)
import           Control.Monad.Supply
import qualified NLIBC.Syntax.Base as NL
import           NLIBC.Syntax.Base
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,singletons)
import           Data.Proxy (Proxy(..))
import           Text.Printf (printf)
import           Unsafe.Coerce (unsafeCoerce)

-- ** Natural Numbers

singletons [d|
  data Nat = Zero | Suc Nat
     deriving (Eq,Show,Ord)
  |]

promote [d|
  (!!) :: [a] -> Nat -> a
  []     !! _     = error "!!: index out of bounds"
  (x:_ ) !! Zero  = x
  (x:xs) !! Suc n = xs !! n
  |]


-- ** Semantic Types

infixr 4 :*
infixr 2 :->

data E
data T

data Univ (t :: *) where
  E     :: Univ E
  T     :: Univ T
  Unit  :: Univ ()
  (:->) :: Univ a -> Univ b -> Univ (a -> b)
  (:*)  :: Univ a -> Univ b -> Univ (a  , b)


pattern ET  = E :-> T
pattern EET = E :-> ET
pattern TT  = T :-> T
pattern TTT = T :-> TT
pattern TET = T :-> ET


class    UnivI t  where univ :: Univ t
instance UnivI E  where univ = E
instance UnivI T  where univ = T
instance UnivI () where univ = Unit

instance (UnivI a, UnivI b) => UnivI (a -> b) where univ = univ :-> univ
instance (UnivI a, UnivI b) => UnivI (a  , b) where univ = univ :*  univ

withUnivI :: Univ a -> (UnivI a => k) -> k
withUnivI (a :-> b) e = withUnivI a (withUnivI b e)
withUnivI (a :*  b) e = withUnivI a (withUnivI b e)
withUnivI Unit      e = e
withUnivI E         e = e
withUnivI T         e = e

-- ** Semantic Expressions

infixl 9 :$, $

type Name = String

data Prim (a :: *) where
  Prim   :: Univ a -> Name -> Prim a
  (:$)   :: Prim (a -> b) -> Expr a -> Prim b
  CaseOf :: Expr (a  , b) -> Expr (b -> a -> c) -> Prim c

type family EXPR (a :: *) where
  EXPR (a -> b) = (Expr a -> Expr b)
  EXPR (a  , b) = (Expr a  , Expr b)
  EXPR ()       = ()
  EXPR E        = E
  EXPR T        = T

data Expr (a :: *) where
  PRIM :: Prim a -> Expr a
  EXPR :: UnivI a => EXPR a -> Expr a


-- |Function application, normalising if possible.
($) :: Expr (a -> b) -> Expr a -> Expr b
EXPR f $ x =      (f    x)
PRIM f $ x = PRIM (f :$ x)


-- |Case analysis, normalising if possible.
caseof :: Expr (a  , b) -> Expr (b -> a -> c) -> Expr c
caseof (EXPR (x, y)) (EXPR f) = case f y of { EXPR g -> g x ; PRIM g -> PRIM (g :$ x) }
caseof xy            f        = PRIM (CaseOf xy f)

fst :: (UnivI a, UnivI b) => Expr (a , b) -> Expr a
fst xy = caseof xy (EXPR(\y -> EXPR(\x -> x)))

snd :: (UnivI a, UnivI b) => Expr (a , b) -> Expr b
snd xy = caseof xy (EXPR(\y -> EXPR(\x -> y)))


-- ** Type Reconstruction

class TypeOf (f :: * -> *) where
  typeof :: f a -> Univ a

instance TypeOf (Prim) where
  typeof (Prim t _)   = t
  typeof (f :$ _)     = case typeof f of (_ :-> b)       -> b
  typeof (CaseOf _ f) = case typeof f of (_ :-> _ :-> c) -> c

instance TypeOf (Expr) where
  typeof (PRIM p) = typeof p
  typeof (EXPR e) = univ


-- ** Haskell Expressions with Environments

newtype Hask ts t = Hask { runHask :: Env ts -> Expr t }

data Env (ts :: [*]) where
  Nil  :: Env '[]
  Cons :: Expr t -> Env ts -> Env (t ': ts)

n0 = SZero
n1 = SSuc n0
n2 = SSuc n1
n3 = SSuc n2
n4 = SSuc n3
n5 = SSuc n4
n6 = SSuc n5
n7 = SSuc n6
n8 = SSuc n7
n9 = SSuc n8

lookup :: SNat n -> Env ts -> Expr (ts :!! n)
lookup  _        Nil        = error "%!!: index out of bounds"
lookup  SZero   (Cons x _ ) = x
lookup (SSuc n) (Cons x xs) = lookup n xs


-- **

not :: Extern T -> Extern T
not x = Not x

exists :: Univ a -> (Extern a -> Extern T) -> Extern T
exists a f = withUnivI a (Exists a (\x -> f (extern a x)))

forall :: Univ a -> (Extern a -> Extern T) -> Extern T
forall a f = withUnivI a (ForAll a (\x -> f (extern a x)))


-- ** Pretty-Printing Expressions

infix  6 :/=, :==
infixr 4 :/\
infixr 2 :=>

pattern x :/= y = x :≢ y
pattern x :== y = x :≡ y
pattern x :/\ y = x :∧ y
pattern x :=> y = x :⊃ y


infix  6 :≢, :≡
infixr 4 :∧
infixr 2 :⊃

pattern x :≢ y     = Not (x :≡ y)
pattern x :≡ y     = PRIM (Prim (E :-> E :-> T)   "≡" :$ x :$ y)
pattern Not  x     = PRIM (Prim (T :-> T)         "¬" :$ x)
pattern x :∧ y     = PRIM (Prim (T :-> T :-> T)   "∧" :$ x :$ y)
pattern x :⊃ y     = PRIM (Prim (T :-> T :-> T)   "⊃" :$ x :$ y)
pattern ForAll t f = PRIM (Prim ((t :-> T) :-> T) "∀" :$ EXPR f)
pattern Exists t f = PRIM (Prim ((t :-> T) :-> T) "∃" :$ EXPR f)


ppPrim :: Int -> Prim a -> Supply Name String
ppPrim d (Prim _ n)    = return n
ppPrim d (f :$ x)      = parens (d > 10) (printf "%s %s" <$> ppPrim 10 f <*> ppExpr 11 x)
ppPrim d (CaseOf xy f) = do x <- supply
                            y <- supply
                            case typeof xy of
                              (a :* b) -> do
                                let x' = PRIM (Prim a x)
                                let y' = PRIM (Prim b y)
                                let f' = (f $ y') $ x'
                                parens (d > 1)
                                  (printf "case %s of (%s,%s) -> %s" <$>
                                    ppExpr 0 xy <*> pure x <*> pure y <*> ppExpr 2 f')


ppExpr :: Int -> Expr a -> Supply Name String
ppExpr d (ForAll t f)         = do x <- supply
                                   parens (d > 1)
                                     (printf "∀%s.%s" x <$> ppExpr 2 (f (PRIM (Prim t x))))
ppExpr d (Exists t f)         = do x <- supply
                                   parens (d > 1)
                                     (printf "∃%s.%s" x <$> ppExpr 2 (f (PRIM (Prim t x))))
ppExpr d (u :≢ v)             = parens (d > 6)  (printf "%s ≢ %s" <$> ppExpr 7 u <*> ppExpr 7 v)
ppExpr d (Not  u)             = parens (d > 8)  (printf    "¬ %s" <$> ppExpr 8 u)
ppExpr d (u :≡ v)             = parens (d > 6)  (printf "%s ≡ %s" <$> ppExpr 7 u <*> ppExpr 7 v)
ppExpr d (u :∧ v)             = parens (d > 2)  (printf "%s ∧ %s" <$> ppExpr 3 u <*> ppExpr 2 v)
ppExpr d (u :⊃ v)             = parens (d > 4)  (printf "%s ⊃ %s" <$> ppExpr 5 u <*> ppExpr 4 v)
ppExpr d (PRIM f)             = ppPrim d f
ppExpr d (EXPR f :: Expr a) = ppEXPR d (univ :: Univ a) f
  where
    ppEXPR :: Int -> Univ a -> EXPR a -> Supply Name String
    ppEXPR d (a :-> b) f       = do x <- supply
                                    parens (d > 1)
                                      (printf "λ%s.%s" x <$> ppExpr d (f (PRIM (Prim a x))))
    ppEXPR d (a :*  b) (x , y) = do printf "(%s,%s)" <$> ppExpr 0 x <*> ppExpr 0 y
    ppEXPR d Unit      ()      = return "()"


-- |Wrap parenthesis around an expression under a functor, if a
--  Boolean flag is true.
parens :: (Functor f) => Bool -> f String -> f String
parens b s = if b then printf "(%s)" <$> s else s


instance Show (Prim t) where
  show = show . PRIM

instance Show (Expr t) where
  show x = evalSupply (ppExpr 0 x) ns
    where
      ns :: [Name]
      ns = [ x | n <- [0..], let x = 'x':show n ]



-- ** Internalising and externalising expressions

type Intern t = Expr t

type family Extern t where
  Extern (a -> b) = (Extern a -> Extern b)
  Extern (a  , b) = (Extern a  , Extern b)
  Extern ()       = Expr ()
  Extern E        = Expr E
  Extern T        = Expr T

type family Lift m t where
  Lift m (a -> b) = (Lift m a -> Lift m b)
  Lift m (a  , b) = (Lift m a  , Lift m b)
  Lift m ()       = m (Expr ())
  Lift m E        = m (Expr E)
  Lift m T        = m (Expr T)

intern :: Univ a -> Extern a -> Intern a
intern E          x    = x
intern T          x    = x
intern Unit       x    = x
intern (a :*  b) (x,y) =
  withUnivI a (withUnivI b (EXPR(intern a x , intern b y)))
intern (a :-> b)  f    =
  withUnivI a (withUnivI b (EXPR(\x -> intern b (f (extern a x)))))

extern :: Univ a -> Intern a -> Extern a
extern E         x = x
extern T         x = x
extern Unit      x = x
extern (a :*  b) x =
  withUnivI a (withUnivI b (extern a (fst x) , extern b (snd x)))
extern (a :-> b) f =
  \x -> extern b (f $ intern a x)

-- lift :: (Monad m) => Proxy m -> Univ a -> Extern a -> Lift m a
-- lift m E          x    = return x
-- lift m T          x    = return x
-- lift m Unit       x    = return x
-- lift m (a :*  b) (x,y) = (lift m a x , lift m b y)
-- lift m (a :-> b)  f    = \x -> _

-- -}
-- -}
-- -}
-- -}
-- -}
