{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE ImplicitParams      #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
module NLIBC.Semantics (HS,HI,HO,H,Lift,not,etaM,module X) where


import           Prelude hiding (Bool,not,(!!),abs,lookup)
import qualified Data.Bool as Bool
import           Control.Monad ((>=>))
import           Control.Monad.Supply
import qualified NLIBC.Syntax.Base as NL
import           NLIBC.Syntax.Base
import           Data.Proxy (Proxy(..))
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,singletons)
import           Text.Printf (printf)
import           Unsafe.Coerce (unsafeCoerce)
import           NLIBC.Semantics.Postulate as X


not :: Expr T -> Expr T
not (EXPR x) = EXPR (Bool.not x)
not       x  = Not x

{-
--exists :: (Monad m, UnivI a) => (Extern a -> m (Expr T)) -> m (Expr T)
--exists f = Return _
-- Exists univ (\x -> _)

--  withUnivI a (Exists a (\x -> f (extern a x)))

forall :: Univ a -> (Extern a -> Extern T) -> Extern T
forall a f = withUnivI a (ForAll a (\x -> f (extern a x)))


infix  6 ≢, ≡
infixr 4 ∧
infixr 2 ⊃

(∧) :: Extern T -> Extern T -> Extern T
EXPR(False) ∧ _           = EXPR(False)
_           ∧ EXPR(False) = EXPR(False)
EXPR(True)  ∧ y           = y
x           ∧ EXPR(True)  = x
x           ∧ y           = x :∧ y

(⊃) :: Extern T -> Extern T -> Extern T
EXPR(False) ⊃ _           = EXPR(True)
EXPR(True)  ⊃ EXPR(True)  = EXPR(True)
EXPR(True)  ⊃ EXPR(False) = EXPR(False)
x           ⊃ y           = x :⊃ y

(≡), (≢) :: Extern E -> Extern E -> Extern T
x ≡ y = x :≡ y
x ≢ y = x :≢ y
-}

-- ** Translation from Syntactic Types into Semantic Types

type family H a where
  H (El S)       = T
  H (El N)       = E -> T
  H (El NP)      = E
  H (El PP)      = E
  H (El INF)     = E -> T
  H (Dia k a)    = H a
  H (Box k a)    = H a
  H (a :& b)     = (H a, H b)
  H (UnitR k a)  = H a
  H (ImpR k a b) = H a -> H b
  H (ImpL k b a) = H a -> H b

type family HI x where
  HI (StI  a)     = H  a
  HI (DIA k x)    = HI x
  HI  B           = ()
  HI  C           = ()
  HI (UNIT k)     = ()
  HI (PROD k x y) = (HI x, HI y)

type family HO x where
  HO (StO  a)     = H  a
  HO (BOX k x)    = HO x
  HO (IMPR k x y) = HI x -> HO y
  HO (IMPL k y x) = HI x -> HO y

type family HS s where
  HS (x :⊢  y)    = HI x -> HO y
  HS (x :⊢> b)    = HI x -> H  b
  HS (a :<⊢ y)    = H  a -> HO y

type family Lift m a where
  Lift m (a -> b) = Lift m a -> m (Lift m b)
  Lift m (a  , b) = (Lift m a , Lift m b)
  Lift m a        = a


-- ** Translation from Syntactic Terms into Semantic Terms
etaM :: (Monad m, ?m :: Proxy m) => Syn s -> Lift m (Extern (HS s))
etaM (AxR   _)   = \x -> return x
etaM (AxL   _)   = \x -> return x
etaM (UnfR  _ f) = etaM f
etaM (UnfL  _ f) = etaM f
etaM (FocR  _ f) = etaM f
etaM (FocL  _ f) = etaM f
etaM (WithL1  f) = \(x,y) -> etaM f x
etaM (WithL2  f) = \(x,y) -> etaM f y
etaM (WithR f g) = \x -> (,) <$> etaM f x <*> etaM g x
etaM (ImpRL f g) = \h -> return (etaM f >=> h >=> etaM g)
etaM (ImpLL f g) = \h -> return (etaM f >=> h >=> etaM g)
etaM (ImpRR f)   = etaM f
etaM (ImpLR f)   = etaM f
etaM (ResRP f)   = \(x,y) -> do f <- etaM f y; f x
etaM (ResLP f)   = \(x,y) -> do f <- etaM f x; f y
etaM (ResPR f)   = \y -> return (\x -> etaM f (x,y))
etaM (ResPL f)   = \x -> return (\y -> etaM f (x,y))
etaM (DiaL  f)   = etaM f
etaM (DiaR  f)   = etaM f
etaM (BoxL  f)   = etaM f
etaM (BoxR  f)   = etaM f
etaM (ResBD f)   = etaM f
etaM (ResDB f)   = etaM f
etaM (ExtRR f)   = \((x,y),z) -> etaM f (x,(y,z))
etaM (ExtLR f)   = \((x,y),z) -> etaM f ((x,z),y)
etaM (ExtLL f)   = \(z,(y,x)) -> etaM f ((z,y),x)
etaM (ExtRL f)   = \(z,(y,x)) -> etaM f (y,(z,x))
etaM (IfxRR f)   = \(x,(y,z)) -> etaM f ((x,y),z)
etaM (IfxLR f)   = \((x,z),y) -> etaM f ((x,y),z)
etaM (IfxLL f)   = \((z,y),x) -> etaM f (z,(y,x))
etaM (IfxRL f)   = \(y,(z,x)) -> etaM f (z,(y,x))
etaM (UnitRL  f) = \x -> etaM f (x,EXPR())
etaM (UnitRR  f) = \(x,_) -> etaM f x
etaM (UnitRI  f) = \(x,_) -> etaM f x
etaM (DnB f)     = \(y,((_,x),z)) -> etaM f (x,(y,z))
etaM (DnC f)     = \(x,((_,y),z)) -> etaM f ((x,y),z)
etaM (UpB f)     = \(x,(y,z)) -> etaM f (y,((EXPR(),x),z))
etaM (UpC f)     = \((x,y),z) -> etaM f (x,((EXPR(),y),z))

-- -}
-- -}
-- -}
-- -}
-- -}
