{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, ScopedTypeVariables, InstanceSigs #-}
module NLIBC.Semantics where


import           Prelude hiding ((!!),abs,pred)
import           Control.Monad.State
import qualified NLIBC.Syntax.Base as NL
import           NLIBC.Syntax.Base (Syn(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,promoteOnly,singletons,singletonsOnly)
import           Text.Printf (printf)
import           Unsafe.Coerce (unsafeCoerce)


data E
data T


singletons [d|

  data Nat = Z | S Nat
     deriving (Eq,Show,Ord)

  |]

promote [d|

  (!!) :: [a] -> Nat -> a
  []     !! _     = error "!!: index out of bounds"
  (x:_ ) !! Z  = x
  (x:xs) !! S n = xs !! n

  |]


class Sem (repr :: [*] -> * -> *) where
  var    :: SNat n -> repr ts (ts :!! n)
  abs    :: repr (t1 ': ts) t2 -> repr ts (t1 -> t2)
  app    :: repr ts (t1 -> t2) -> repr ts t1 -> repr ts t2
  unit   :: repr ts ()
  pair   :: repr ts t1 -> repr ts t2 -> repr ts (t1, t2)
  proj1  :: repr ts (t1, t2) -> repr ts t1
  proj1  x   = caseof x v0
  proj2  :: repr ts (t1, t2) -> repr ts t2
  proj2  x   = caseof x v1
  caseof :: repr ts (t1, t2) -> repr (t1 ': t2 ': ts) t3 -> repr ts t3
  caseof x f = abs (abs f) `app` proj2 x `app` proj1 x


v0 :: Sem repr => repr (t0 ': ts) t0
v0  = var SZ
v1 :: Sem repr => repr (t0 ': t1 ': ts) t1
v1  = var (SS SZ)
v2 :: Sem repr => repr (t0 ': t1 ': t2 ': ts) t2
v2  = var (SS (SS SZ))
v3 :: Sem repr => repr (t0 ': t1 ': t2 ': t3 ': ts) t3
v3  = var (SS (SS (SS SZ)))
v4 :: Sem repr => repr (t0 ': t1 ': t2 ': t3 ': t4 ': ts) t4
v4  = var (SS (SS (SS (SS SZ))))
v5 :: Sem repr => repr (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': ts) t5
v5  = var (SS (SS (SS (SS (SS SZ)))))


type family H a where
  H (NL.El NL.S)     = T
  H (NL.El NL.N)     = (E -> T)
  H (NL.El NL.NP)    = E
  H (NL.El NL.PP)    = E
  H (NL.El NL.INF)   = (E -> T)
  H (NL.Dia k a)     = H a
  H (NL.Box k a)     = H a
  H (a NL.:& b)      = (H a, H b)
  H (NL.UnitR k a)   = H a
  H (NL.ImpR k a b)  = H a -> H b
  H (NL.ImpL k b a)  = H a -> H b

type family HI x where
  HI (NL.StI  a)     = H  a
  HI (NL.DIA k x)    = HI x
  HI  NL.B           = ()
  HI  NL.C           = ()
  HI (NL.UNIT k)     = ()
  HI (NL.PROD k x y) = (HI x, HI y)

type family HO x where
  HO (NL.StO  a)     = H  a
  HO (NL.BOX k x)    = HO x
  HO (NL.IMPR k x y) = HI x -> HO y
  HO (NL.IMPL k y x) = HI x -> HO y

type family HS s where
  HS (x NL.:⊢  y)    = HI x -> HO y
  HS (x NL.:⊢> b)    = HI x -> H  b
  HS (a NL.:<⊢ y)    = H  a -> HO y


eta :: Sem repr => Syn s -> repr ts (HS s)
eta (AxR     _) = abs v0
eta (AxL     _) = abs v0
eta (UnfR  _ f) = eta f
eta (UnfL  _ f) = eta f
eta (FocR  _ f) = eta f
eta (FocL  _ f) = eta f
eta (WithL1  f) = abs (eta f `app` proj1 v0)
eta (WithL2  f) = abs (eta f `app` proj2 v0)
eta (WithR f g) = abs (pair (eta f `app` v0) (eta g `app` v0))
eta (ImpRL f g) = abs (abs (eta g `app` (v1 `app` (eta f `app` v0))))
eta (ImpRR   f) = eta f
eta (ImpLL f g) = abs (abs (eta g `app` (v1 `app` (eta f `app` v0))))
eta (ImpLR   f) = eta f
eta (Res11   f) = abs (caseof v0 ((eta f `app` v1) `app` v0))
eta (Res12   f) = abs (abs (eta f `app` (pair v0 v1)))
eta (Res13   f) = abs (caseof v0 ((eta f `app` v0) `app` v1))
eta (Res14   f) = abs (abs (eta f `app` (pair v1 v0)))
eta (DiaL    f) = eta f
eta (DiaR    f) = eta f
eta (BoxL    f) = eta f
eta (BoxR    f) = eta f
eta (Res21   f) = eta f
eta (Res22   f) = eta f
eta (UnitRL  f) = abs (eta f `app` pair v0 unit)
eta (UnitRR  f) = abs (caseof v0 (eta f `app` v0))
eta (UnitRI  f) = abs (caseof v0 (eta f `app` v0))
eta (ExtLL   f) = abs (caseof v0 (caseof v1 (eta f `app` pair (pair v2 v0) v1)))
eta (ExtLR   f) = abs (caseof v0 (caseof v0 (eta f `app` pair (pair v0 v3) v1)))
eta (ExtRL   f) = abs (caseof v0 (caseof v1 (eta f `app` pair v0 (pair v2 v1))))
eta (ExtRR   f) = abs (caseof v0 (caseof v0 (eta f `app` pair v0 (pair v1 v3))))
eta (IfxLL   f) = abs (caseof v0 (caseof v0 (eta f `app` pair v0 (pair v1 v3))))
eta (IfxLR   f) = abs (caseof v0 (caseof v0 (eta f `app` pair (pair v0 v3) v1)))
eta (IfxRL   f) = abs (caseof v0 (caseof v1 (eta f `app` pair v0 (pair v2 v1))))
eta (IfxRR   f) = abs (caseof v0 (caseof v1 (eta f `app` pair (pair v2 v0) v1)))
eta (DnB     f) = abs (caseof v0 (caseof v1 (eta f `app` pair (proj2 v0) (pair v2 v1))))
eta (UpB     f) = abs (caseof v0 (caseof v1 (eta f `app` pair v0 (pair (pair unit v2) v1))))
eta (DnC     f) = abs (caseof v0 (caseof v1 (eta f `app` pair (pair v2 (proj2 v0)) v1)))
eta (UpC     f) = abs (caseof v0 (caseof v0 (eta f `app` pair v0 (pair (pair unit v1) v3))))


-- * Translate to Haskell

type family ToHask t where
  ToHask E        = Int
  ToHask T        = Bool
  ToHask ()       = ()
  ToHask (a -> b) = ToHask a -> ToHask b
  ToHask (a ,  b) = (ToHask a, ToHask b)

data Env (ts :: [*]) where
  Nil  :: Env '[]
  Cons :: ToHask t -> Env ts -> Env (t ': ts)

(%!!) :: Env ts -> SNat n -> ToHask (ts :!! n)
(%!!)  Nil         _     = error "%!!: index out of bounds"
(%!!) (Cons x _ )  SZ    = x
(%!!) (Cons x xs) (SS n) = xs %!! n

newtype Hask (ts :: [*]) (t :: *) = Hask { runHask :: Env ts -> ToHask t }

instance Sem Hask where
  var    n   = Hask $ \env -> env %!! n
  abs    f   = Hask $ \env -> \x -> runHask f (Cons x env)
  app    f x = Hask $ \env -> runHask f env (runHask x env)
  unit       = Hask $ const ()
  pair   x y = Hask $ \env -> (runHask x env , runHask y env)
  proj1  p   = Hask $ \env -> fst (runHask p env)
  proj2  p   = Hask $ \env -> snd (runHask p env)
  caseof p f = Hask $ \env ->
    case (runHask p env) of (x,y) -> runHask f (Cons x (Cons y env))

eval :: ToHask (HI x) -> Syn (x NL.:⊢ y) -> ToHask (HO y)
eval x f = runHask (eta f `app` (Hask (const x))) Nil


-- -}
-- -}
-- -}
-- -}
-- -}
