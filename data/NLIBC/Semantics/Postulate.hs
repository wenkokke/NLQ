{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE ImplicitParams        #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module NLIBC.Semantics.Postulate where


import           Prelude hiding ((!!),abs,lookup)
import           Control.Monad (join)
import           Control.Monad.Supply
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,singletons)
import           Data.Proxy (Proxy(..))
import           Data.Void (Void)
import           Text.Printf (printf)
import           Unsafe.Coerce (unsafeCoerce)


-- ** Semantic Types

data E
data T

data (m :: * -> *) :@ (a :: *)


-- ** Singletons for semantic types

data Univ (m :: * -> *) (t :: *) where
  E     :: Univ m E
  T     :: Univ m T
  U     :: Univ m ()
  M     :: Univ m a -> Univ m (m :@ a)
  (:->) :: Univ m a -> Univ m b -> Univ m (a -> b)
  (:*)  :: Univ m a -> Univ m b -> Univ m (a  , b)


-- ** Singleton instance derivation for semantic types

class UnivI m t where univ :: Univ m t
instance UnivI m E where univ = E
instance UnivI m T where univ = T
instance UnivI m () where univ = U
instance (UnivI m a) => UnivI m (m :@ a) where univ = M univ
instance (UnivI m a, UnivI m b) => UnivI m (a -> b) where univ = univ :-> univ
instance (UnivI m a, UnivI m b) => UnivI m (a  , b) where univ = univ :*  univ

withUniv :: Univ m a -> (UnivI m a => b) -> b
withUniv E         x = x
withUniv T         x = x
withUniv U         x = x
withUniv (M a)     x = withUniv a x
withUniv (a :* b)  x = withUniv a (withUniv b x)
withUniv (a :-> b) x = withUniv a (withUniv b x)


-- ** Expressions

type Name = String

data Prim (m :: * -> *) (t :: *) where
  Prim   :: Univ m a        -> Name                 -> Prim m a
  (:$)   :: Prim m (a -> b) -> Expr m a             -> Prim m b
  CaseOf :: Prim m (a , b)  -> Expr m (b -> a -> c) -> Prim m c
  Bind   :: Prim m (m :@ a) -> Expr m (a -> m :@ b) -> Prim m (m :@ b)
  Join   :: Expr m (m :@ (m :@ a)) -> Prim m (m :@ a)
  Return :: Prim m a -> Prim m (m :@ a)

data Expr (m :: * -> *) (t :: *) where
  PRIM :: Prim  m t -> Expr m t
  EXPR :: UnivI m t => EXPR m t -> Expr m t

type family EXPR (m :: * -> *) (t :: *) where
  EXPR m (a -> b) = Expr m a -> Expr m b
  EXPR m (a  , b) = (Expr m a , Expr m b)
  EXPR m (m :@ a) = m (Expr m a)
  EXPR m ()       = ()
  EXPR m E        = Void
  EXPR m T        = Bool


forall :: (UnivI m a) => (Expr m a -> Expr m (m :@ T)) -> Expr m (m :@ T)
forall f = PRIM(Prim ((univ :-> M T) :-> M T) "forall" :$ EXPR f)

exists :: (UnivI m a) => (Expr m a -> Expr m (m :@ T)) -> Expr m (m :@ T)
exists f = PRIM(Prim ((univ :-> M T) :-> M T) "exists" :$ EXPR f)


-- ** Typing function

class TypeOf f where
  typeof :: f m t -> Univ m t

instance TypeOf Prim where
  typeof (Prim a _)   = a
  typeof (f :$ _)     = case typeof f of { (a :-> b) -> b }
  typeof (CaseOf p f) = case typeof f of { (b :-> (a :-> c)) -> c }

instance TypeOf Expr where
  typeof (PRIM x) = typeof x
  typeof (EXPR _) = univ


-- ** Externalise expressions

apply :: Expr m (a -> b) -> Expr m a -> Expr m b
EXPR f `apply` x =      (f    x)
PRIM f `apply` x = PRIM (f :$ x)

caseof :: Expr m (a , b) -> Expr m (b -> a -> c) -> Expr m c
caseof (EXPR(x,y)) (EXPR f) = case f y of EXPR g -> g x; PRIM g -> PRIM (g :$ x)
caseof (EXPR(x,y)) (PRIM f) = PRIM ((f :$ y) :$ x)
caseof (PRIM p)          f  = PRIM (CaseOf p f)

bind :: (Monad m) => Expr m (m :@ a) -> Expr m (a -> m :@ b) -> Expr m (m :@ b)
bind (EXPR x) f =
  case typeof f of (a :-> M b) -> withUniv b (PRIM(Join(EXPR (apply f <$> x))))
bind (PRIM x) f = PRIM(Bind x f)

retn :: (Monad m) => Expr m a -> Expr m (m :@ a)
retn x@(EXPR _) = EXPR(return x)
retn   (PRIM x) = PRIM(Return x)


type family Hask m t where
  Hask m (a -> b) = (Hask m a -> Hask m b)
  Hask m (a  , b) = (Hask m a  , Hask m b)
  Hask m (m :@ a) = m (Hask m a)
  Hask m ()       = ()
  Hask m E        = Expr m E
  Hask m T        = Expr m T


fromHask :: (Functor m) => Univ m a -> Hask m a -> Expr m a
fromHask E          x    = x
fromHask T          x    = x
fromHask U          _    = EXPR()
fromHask (M a)      x    =
  withUniv a (EXPR(fromHask a <$> x))
fromHask (a :*  b) (x,y) =
  withUniv a (withUniv b (EXPR(fromHask a x , fromHask b y)))
fromHask (a :-> b)  f    =
  withUniv a (withUniv b (EXPR(\x -> fromHask b (f (toHask a x)))))


toHask :: (Functor m) => Univ m a -> Expr m a -> Hask m a
toHask E         x = x
toHask T         x = x
toHask U         _ = ()
toHask (M a)     x =
  _
toHask (a :* b)  p =
  withUniv a (withUniv b
              (toHask a (caseof p (EXPR(\y -> EXPR(\x -> x))))
              ,toHask b (caseof p (EXPR(\y -> EXPR(\x -> y))))))
toHask (a :-> b) f =
  \x -> toHask b (f `apply` fromHask a x)

{-





{-
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
data M a

data Univ (m :: * -> *) (t :: *) where
  E     :: Univ m E
  T     :: Univ m T
  U     :: Univ m ()
  M     :: Univ m a -> Univ m (M a)
  (:->) :: Univ m a -> Univ m b -> Univ m (a -> b)
  (:*)  :: Univ m a -> Univ m b -> Univ m (a  , b)


pattern ET  = E :-> T
pattern EET = E :-> ET
pattern TT  = T :-> T
pattern TTT = T :-> TT
pattern TET = T :-> ET
pattern ETT = E :-> TT


class                              UnivI m t        where univ :: Univ m t
instance                           UnivI m E        where univ = E
instance                           UnivI m T        where univ = T
instance                           UnivI m ()       where univ = U
instance (UnivI m a)            => UnivI m (M a)    where univ = M univ
instance (UnivI m a, UnivI m b) => UnivI m (a -> b) where univ = univ :-> univ
instance (UnivI m a, UnivI m b) => UnivI m (a  , b) where univ = univ :*  univ

withUnivI :: Univ m a -> (UnivI m a => k) -> k
withUnivI (a :-> b) e = withUnivI a (withUnivI b e)
withUnivI (a :*  b) e = withUnivI a (withUnivI b e)
withUnivI U         e = e
withUnivI E         e = e
withUnivI T         e = e

-- ** Semantic Expressions

infixl 9 :$

type Name = String

data Prim (m :: * -> *) (a :: *) where
  Prim   :: Univ m a        -> Name                 -> Prim m a
  (:$)   :: Prim m (a -> b) -> Expr m a             -> Prim m b
  CaseOf :: Expr m (a  , b) -> Expr m (b -> a -> c) -> Prim m c
  (:>>=) :: Expr m (M a)    -> Expr m (a -> M b)    -> Prim m (M b)
  Return :: Prim m a        -> Prim m (M a)

type family EXPR (m :: * -> *) (a :: *) where
  EXPR m (a -> b) = Expr m a -> Expr m b
  EXPR m (a  , b) = (Expr m a , Expr m b)
  EXPR m (M a)    = m (Expr m a)
  EXPR m ()       = ()
  EXPR m E        = Void
  EXPR m T        = Bool

data Expr (m :: * -> *) (a :: *) where
  PRIM :: Prim m a -> Expr m a
  EXPR :: UnivI m a => EXPR m a -> Expr m a


-- ** Functions which normalise

apply :: Expr m (a -> b) -> Expr m a -> Expr m b
EXPR f `apply` x =      (f    x)
PRIM f `apply` x = PRIM (f :$ x)

caseof :: Expr m (a , b) -> Expr m (b -> a -> c) -> Expr m c
caseof (EXPR (x, y)) (EXPR f) = case f y of { EXPR g -> g x ; PRIM g -> PRIM (g :$ x) }
caseof xy            f        = PRIM (CaseOf xy f)

--fst' :: (UnivI m a, UnivI m b) => Expr m (a , b) -> Expr m a
--fst' xy = caseof' xy (EXPR(\y -> EXPR(\x -> x)))
--snd' :: (UnivI m a, UnivI m b) => Expr m (a , b) -> Expr m b
--snd' xy = caseof' xy (EXPR(\y -> EXPR(\x -> y)))

retn :: (Monad m) => Expr m a -> Expr m (M a)
retn x@(EXPR _) = EXPR(return x)
retn   (PRIM x) = PRIM(Return x)

bind :: (Monad m) => Expr m (M a) -> Expr m (a -> M b) -> Expr m (M b)
bind (EXPR x :: Expr m (M a)) (EXPR f :: Expr m (a -> M b))
  = EXPR(do { x <- x
            ; let
                g :: Expr m (M b)
                g = f x
            ; case g of
              EXPR h -> h
              PRIM h -> _
            })
bind x        f        = PRIM(x :>>= f)



{-
-- ** Type Reconstruction

class TypeOf (f :: * -> *) where
  typeof :: f a -> Univ a

instance TypeOf (Prim m) where
  typeof (Prim m t _)   = t
  typeof (f :$ _)     = case typeof f of (_ :-> b)       -> b
  typeof (CaseOf _ f) = case typeof f of (_ :-> _ :-> c) -> c

instance TypeOf (Expr m) where
  typeof (PRIM p) = typeof p
  typeof (EXPR e) = univ


-- ** Haskell Expr messions with Environments

newtype Hask ts t = Hask { runHask :: Env ts -> Expr m t }

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

-- ** Pretty-Printing Expressions

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
                                let f' = app' (app' f y') x'
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
    ppEXPR d U         ()      = return "()"


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
  Extern (m    a) = m (Extern a)
  Extern ()       = Expr ()
  Extern E        = Expr E
  Extern T        = Expr T


intern :: Univ a -> Extern a -> Intern a
intern E          x    = x
intern T          x    = x
intern U          x    = x
intern (a :*  b) (x,y) =
  withUnivI a (withUnivI b (EXPR(intern a x , intern b y)))
intern (a :-> b)  f    =
  withUnivI a (withUnivI b (EXPR(\x -> intern b (f (extern a x)))))


extern :: Univ a -> Intern a -> Extern a
extern E         x     = x
extern T         x     = x
extern U         x     = x
extern (a :*  b) xy    =
  withUnivI a (withUnivI b (extern a (fst' xy) , extern b (snd' xy)))
extern (a :-> b) f     =
  \x -> extern b (app' f (intern a x))


-- -}
-- -}
-- -}
-- -}
