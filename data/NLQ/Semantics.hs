{-# LANGUAGE GADTs          #-}
{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE ImplicitParams #-}
module NLQ.Semantics
       (HS,HI,HO,H,withHS,withHI,withHO,withH,hs,hi,ho,h,eta,Lift,etaM) where


import           Control.Monad ((>=>))
import           Data.Proxy (Proxy(..))

import qualified NLQ.Syntax.Base as NL
import           NLQ.Syntax.Base
import           NLQ.Semantics.Postulate as X


-- ** Translation from Syntactic Types into Semantic Types

type family H a where
  H (El S)       = T
  H (El N)       = (E -> T)
  H (El NP)      = E
  H (El PP)      = E
  H (El INF)     = (E -> T)
  H (Dia k a)    = H a
  H (Box k a)    = H a
  H (a :& b)     = (H a, H b)
  H (UnitL k a)  = H a
  H (ImpR k a b) = H a -> H b
  H (ImpL k b a) = H a -> H b

type family HI x where
  HI (StI  a)     = H  a
  HI (DIA k x)    = HI x
  HI  B           = ()
  HI  C           = ()
  HI  I'          = ()
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

withH :: SType t -> (UnivI (H t) => a) -> a
withH (SEl SS)       k = k
withH (SEl SN)       k = k
withH (SEl SNP)      k = k
withH (SEl SPP)      k = k
withH (SEl SINF)     k = k
withH (SDia _ a)     k = withH a k
withH (SBox _ a)     k = withH a k
withH (a :%& b)      k = withH a (withH b k)
withH (SUnitL _ a)   k = withH a k
withH (SImpR  _ a b) k = withH a (withH b k)
withH (SImpL  _ b a) k = withH a (withH b k)

withHI :: SStructI x -> (UnivI (HI x) => a) -> a
withHI (SStI    a)   k = withH  a k
withHI (SDIA _  x)   k = withHI x k
withHI  SB           k = k
withHI  SC           k = k
withHI (SUNIT _)     k = k
withHI (SPROD _ x y) k = withHI x (withHI y k)

withHO :: SStructO y -> (UnivI (HO y) => a) -> a
withHO (SStO    a)   k = withH  a k
withHO (SBOX  _ x)   k = withHO x k
withHO (SIMPR _ x y) k = withHI x (withHO y k)
withHO (SIMPL _ y x) k = withHI x (withHO y k)

withHS :: SSequent s -> (UnivI (HS s) => a) -> a
withHS (x :%⊢  y)    k = withHI x (withHO y k)
withHS (x :%⊢> b)    k = withHI x (withH  b k)
withHS (a :%<⊢ y)    k = withH  a (withHO y k)

h :: SType t -> Univ (H t)
h t = withH t univ

hi :: SStructI x -> Univ (HI x)
hi x = withHI x univ

ho :: SStructO y -> Univ (HO y)
ho y = withHO y univ

hs :: SSequent s -> Univ (HS s)
hs s = withHS s univ


-- ** Translation from syntactic terms into semantic terms

eta :: Syn s -> Hask (HS s)
eta (AxR   _)   = \x -> x
eta (AxL   _)   = \x -> x
eta (UnfR  _ f) = eta f
eta (UnfL  _ f) = eta f
eta (FocR  _ f) = eta f
eta (FocL  _ f) = eta f
eta (WithL1  f) = \(x,y) -> eta f x
eta (WithL2  f) = \(x,y) -> eta f y
eta (WithR f g) = \x -> (eta f x, eta g x)
eta (ImpRL f g) = \h -> eta g . h . eta f
eta (ImpLL f g) = \h -> eta g . h . eta f
eta (ImpRR f)   = eta f
eta (ImpLR f)   = eta f
eta (ResRP f)   = \(x,y) -> eta f  y x
eta (ResLP f)   = \(x,y) -> eta f  x y
eta (ResPR f)   = \ y x  -> eta f (x,y)
eta (ResPL f)   = \ x y  -> eta f (x,y)
eta (DiaL  f)   = eta f
eta (DiaR  f)   = eta f
eta (BoxL  f)   = eta f
eta (BoxR  f)   = eta f
eta (ResBD f)   = eta f
eta (ResDB f)   = eta f
eta (ExtRR f)   = \((x,y),z) -> eta f (x,(y,z))
eta (ExtLR f)   = \((x,y),z) -> eta f ((x,z),y)
eta (ExtLL f)   = \(z,(y,x)) -> eta f ((z,y),x)
eta (ExtRL f)   = \(z,(y,x)) -> eta f (y,(z,x))
eta (IfxRR f)   = \(x,(y,z)) -> eta f ((x,y),z)
eta (IfxLR f)   = \((x,z),y) -> eta f ((x,y),z)
eta (IfxLL f)   = \((z,y),x) -> eta f (z,(y,x))
eta (IfxRL f)   = \(y,(z,x)) -> eta f (z,(y,x))
eta (UnitLL  f) = \x -> eta f (EXPR(),x)
eta (UnitLR  f) = \(_,x) -> eta f x
eta (UnitLI  f) = \(_,x) -> eta f x
eta (DnB  f)     = \(((_,x),y),z) -> eta f (x,(y,z))
eta (DnC  f)     = \(((_,x),z),y) -> eta f ((x,y),z)
eta (UpB  f)     = \(x,(y,z)) -> eta f (((EXPR(),x),y),z)
eta (DnI' f)     = \((_,x),y) -> eta f (x,y)
eta (UpC  f)     = \((x,y),z) -> eta f (((EXPR(),x),z),y)
eta (UpI' f)     = \(x,y) -> eta f ((EXPR(),x),y)



-- ** Translation from syntactic terms into monadic semantic terms

type family Lift m a where
  Lift m (a -> b) = Lift m a -> m (Lift m b)
  Lift m (a  , b) = (Lift m a , Lift m b)
  Lift m a        = a

etaM :: (Monad m, ?m :: Proxy m) => Syn s -> Lift m (Hask (HS s))
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
etaM (UnitLL  f) = \x -> etaM f (EXPR(),x)
etaM (UnitLR  f) = \(_,x) -> etaM f x
etaM (UnitLI  f) = \(_,x) -> etaM f x
etaM (DnB  f)    = \(((_,x),y),z) -> etaM f (x,(y,z))
etaM (DnC  f)    = \(((_,x),z),y) -> etaM f ((x,y),z)
etaM (DnI' f)     = \((_,x),y) -> etaM f (x,y)
etaM (UpB  f)    = \(x,(y,z)) -> etaM f (((EXPR(),x),y),z)
etaM (UpC  f)    = \((x,y),z) -> etaM f (((EXPR(),x),z),y)
etaM (UpI' f)     = \(x,y) -> etaM f ((EXPR(),x),y)

-- -}
-- -}
-- -}
-- -}
-- -}
