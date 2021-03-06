{-# LANGUAGE GADTs            #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}
{-# LANGUAGE FlexibleContexts #-}
module NLQ.Semantics
       (HS,HI,HO,H,withHS,withHI,withHO,withH,hs,hi,ho,h,eta) where


import NLQ.Syntax.Base
import NLQ.Semantics.Postulate as X


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


h  :: SType t -> Univ (H t)
h  t = withH t univ
hi :: SStructI x -> Univ (HI x)
hi x = withHI x univ
ho :: SStructO y -> Univ (HO y)
ho y = withHO y univ
hs :: SSequent s -> Univ (HS s)
hs s = withHS s univ


-- ** Translation from syntactic terms into semantic terms

eta :: Syn s -> Hask (HS s)
eta (AxR   _)    = \x -> x
eta (AxL   _)    = \x -> x
eta (UnfR  _ f)  = eta f
eta (UnfL  _ f)  = eta f
eta (FocR  _ f)  = eta f
eta (FocL  _ f)  = eta f
eta (WthL1P _ f) = \(x,y) -> eta f x
eta (WthL1N _ f) = \(x,y) -> eta f x
eta (WthL2P _ f) = \(x,y) -> eta f y
eta (WthL2N _ f) = \(x,y) -> eta f y
eta (WthR  f g)  = \x -> (eta f x, eta g x)
eta (WthRF f g)  = \x -> (eta f x, eta g x)
eta (ImpRL f g)  = \h -> eta g . h . eta f
eta (ImpLL f g)  = \h -> eta g . h . eta f
eta (ImpRR f)    = eta f
eta (ImpLR f)    = eta f
eta (ResRP f)    = \(x,y) -> eta f  y x
eta (ResLP f)    = \(x,y) -> eta f  x y
eta (ResPR f)    = \ y x  -> eta f (x,y)
eta (ResPL f)    = \ x y  -> eta f (x,y)
eta (DiaL  f)    = eta f
eta (DiaR  f)    = eta f
eta (BoxL  f)    = eta f
eta (BoxR  f)    = eta f
eta (ResBD f)    = eta f
eta (ResDB f)    = eta f
eta (IfxRR f)    = \((x,y),z) -> eta f (x,(y,z))
eta (IfxLR f)    = \((x,y),z) -> eta f ((x,z),y)
eta (IfxLL f)    = \(z,(y,x)) -> eta f ((z,y),x)
eta (IfxRL f)    = \(z,(y,x)) -> eta f (y,(z,x))
eta (ExtRR f)    = \(x,(y,z)) -> eta f ((x,y),z)
eta (ExtLR f)    = \((x,z),y) -> eta f ((x,y),z)
eta (ExtLL f)    = \((z,y),x) -> eta f (z,(y,x))
eta (ExtRL f)    = \(y,(z,x)) -> eta f (z,(y,x))
eta (UnitLL  f)  = \x -> eta f (EXPR(),x)
eta (UnitLR  f)  = \(_,x) -> eta f x
eta (UnitLI  f)  = \(_,x) -> eta f x
eta (DnB  f)     = \(((_,x),y),z) -> eta f (x,(y,z))
eta (DnC  f)     = \(((_,x),z),y) -> eta f ((x,y),z)
eta (UpB  f)     = \(x,(y,z)) -> eta f (((EXPR(),x),y),z)
eta (DnI' f)     = \((_,x),y) -> eta f (x,y)
eta (UpC  f)     = \((x,y),z) -> eta f (((EXPR(),x),z),y)
eta (UpI' f)     = \(x,y) -> eta f ((EXPR(),x),y)

-- -}
-- -}
-- -}
-- -}
-- -}
