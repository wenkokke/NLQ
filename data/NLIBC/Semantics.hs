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
{-# LANGUAGE UndecidableInstances #-}
module NLIBC.Semantics
       (Sem,eta,HS,HI,HO,H,withHS,withHI,withHO,withH,hs,hi,ho,h) where


import           Prelude hiding ((!!),abs,lookup)
import           Control.Monad.Supply
import qualified NLIBC.Syntax.Base as NL
import           NLIBC.Syntax.Base
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,singletons)
import           Text.Printf (printf)
import           Unsafe.Coerce (unsafeCoerce)
import           NLIBC.Semantics.Postulate (E,T,Name,Prim(..),Expr(..),EXPR
                                           ,Env(..),SNat,(:!!),UnivI(..),Univ(..)
                                           ,Hask(..),TypeOf(..),lookup
                                           ,n0,n1,n2,n3,n4,n5,n6,n7,n8,n9)
import qualified NLIBC.Semantics.Postulate as P


-- ** Abstract Semantic Expressions

class Sem repr where
  var    :: (UnivI (ts :!! n))
         => SNat n -> repr ts (ts :!! n)
  abs    :: (UnivI t1, UnivI t2)
         => repr (t1 ': ts) t2 -> repr ts (t1 -> t2)
  app    :: repr ts (t1 -> t2) -> repr ts t1 -> repr ts t2
  unit   :: repr ts ()
  pair   :: (UnivI t1, UnivI t2)
         => repr ts t1 -> repr ts t2 -> repr ts (t1, t2)
  caseof :: (UnivI t1, UnivI t2, UnivI t3)
         => repr ts (t1, t2) -> repr (t1 ': t2 ': ts) t3 -> repr ts t3

  proj1  :: (UnivI t1, UnivI t2)
         => repr ts (t1, t2) -> repr ts t1
  proj1  x = caseof x v0
  proj2  :: (UnivI t1, UnivI t2)
         => repr ts (t1, t2) -> repr ts t2
  proj2  x = caseof x v1

  v0  :: UnivI t0 => repr (t0 ': ts) t0
  v0   = var n0
  v1  :: UnivI t1 => repr (t0 ': t1 ': ts) t1
  v1   = var n1
  v2  :: UnivI t2 => repr (t0 ': t1 ': t2 ': ts) t2
  v2   = var n2
  v3  :: UnivI t3 => repr (t0 ': t1 ': t2 ': t3 ': ts) t3
  v3   = var n3
  v4  :: UnivI t4 => repr (t0 ': t1 ': t2 ': t3 ': t4 ': ts) t4
  v4   = var n4
  v5  :: UnivI t5 => repr (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': ts) t5
  v5   = var n5
  v6  :: UnivI t6 => repr (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': t6 ': ts) t6
  v6   = var n6
  v7  :: UnivI t7 => repr (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': t6 ': t7 ': ts) t7
  v7   = var n7
  v8  :: UnivI t8 => repr (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': t6 ': t7 ': t8 ': ts) t8
  v8   = var n8
  v9  :: UnivI t9 => repr (t0 ': t1 ': t2 ': t3 ': t4 ': t5 ': t6 ': t7 ': t8 ': t9 ': ts) t9
  v9   = var n9


instance Sem Hask where
  var    n                  = Hask (\env -> lookup n env)
  abs    (Hask f)           = Hask (\env -> EXPR(\x -> f (Cons x env)))
  app    (Hask f)  (Hask x) = Hask (\env -> f env `P.app'` x env)
  unit                      = Hask (\env -> EXPR())
  pair   (Hask x)  (Hask y) = Hask (\env -> EXPR(x env, y env))
  caseof (Hask xy)       f  =
    case abs (abs f) of Hask f' -> Hask (\env -> P.caseof' (xy env) (f' env))


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


withH :: SType t -> (UnivI (H t) => a) -> a
withH (SEl SS)       k = k
withH (SEl SN)       k = k
withH (SEl SNP)      k = k
withH (SEl SPP)      k = k
withH (SEl SINF)     k = k
withH (SDia _ a)     k = withH a k
withH (SBox _ a)     k = withH a k
withH (a :%& b)      k = withH a (withH b k)
withH (SUnitR _ a)   k = withH a k
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

eta :: Sem repr => SSequent s -> Syn s -> repr ts (HS s)

-- Axioms and focusing
eta (SStI b1 :%⊢> b2) (AxR   _)   = withH b1 (withH b2 (abs v0))
eta (a1 :%<⊢ SStO a2) (AxL   _)   = withH a1 (withH a2 (abs v0))
eta (x :%⊢> b)        (UnfR  _ f) = eta (x :%⊢ SStO b) f
eta (a :%<⊢ y)        (UnfL  _ f) = eta (SStI a :%⊢ y) f
eta (x :%⊢ SStO b)    (FocR  _ f) = eta (x :%⊢> b) f
eta (SStI a :%⊢ y)    (FocL  _ f) = eta (a :%<⊢ y) f

-- With
eta (SStI (a1 :%& a2) :%⊢ y) (WithL1  f)  =
  withH a1 (withH a2 (withHO y (
    abs (eta (a1 :%<⊢ y) f `app` proj1 v0))))
eta (SStI (a1 :%& a2) :%⊢ y) (WithL2  f)  =
  withH a1 (withH a2 (withHO y (
    abs (eta (a2 :%<⊢ y) f `app` proj2 v0))))
eta (x :%⊢> b1 :%& b2) (WithR f g)  =
  withH b1 (withH b2 (withHI x (
    abs (pair (eta (x :%⊢ SStO b1) f `app` v0) (eta (x :%⊢ SStO b2) g `app` v0)))))

-- Left and right implication, and products
eta (SImpR _ a b :%<⊢ SIMPR _ x y) (ImpRL f g) =
  withH a (withH b (withHI x (withHO y (
    abs (abs (eta (b :%<⊢ y) g `app` (v1 `app` (eta (x :%⊢> a) f `app` v0))))))))
eta (SImpL _ b a :%<⊢ SIMPL _ y x) (ImpLL f g) =
  withH a (withH b (withHI x (withHO y (
    abs (abs (eta (b :%<⊢ y) g `app` (v1 `app` (eta (x :%⊢> a) f `app` v0))))))))

eta (x :%⊢ SStO (SImpR k a b)) (ImpRR f) = eta (x :%⊢ SIMPR k (SStI a) (SStO b)) f
eta (x :%⊢ SStO (SImpL k b a)) (ImpLR f) = eta (x :%⊢ SIMPL k (SStO b) (SStI a)) f

eta (SPROD k x y :%⊢ z) (ResRP f) =
  withHI x (withHI y (withHO z (
    abs (caseof v0 ((eta (y :%⊢ SIMPR k x z) f `app` v1) `app` v0)))))
eta (SPROD k x y :%⊢ z) (ResLP f) =
  withHI x (withHI y (withHO z (
    abs (caseof v0 ((eta (x :%⊢ SIMPL k z y) f `app` v0) `app` v1)))))
eta (y :%⊢ SIMPR k x z) (ResPR f) =
  withHI x (withHI y (withHO z (
    abs (abs (eta (SPROD k x y :%⊢ z) f `app` (pair v0 v1))))))
eta (x :%⊢ SIMPL k z y) (ResPL f) =
  withHI x (withHI y (withHO z (
    abs (abs (eta (SPROD k x y :%⊢ z) f `app` (pair v1 v0))))))

-- Diamond and box
eta (SStI (SDia k a) :%⊢ y)  (DiaL  f) = eta (SDIA k (SStI a) :%⊢ y) f
eta (SDIA _ x :%⊢> SDia _ b) (DiaR  f) = eta (x :%⊢> b) f
eta (SBox _ a :%<⊢ SBOX _ y) (BoxL  f) = eta (a :%<⊢ y) f
eta (x :%⊢ SStO (SBox k b))  (BoxR  f) = eta (x :%⊢ SBOX k (SStO b)) f
eta (SDIA k x :%⊢ y)         (ResBD f) = eta (x :%⊢ SBOX k y) f
eta (x :%⊢ SBOX k y)         (ResDB f) = eta (SDIA k x :%⊢ y) f

-- Extraction
eta ((x :%∙ y) :%∙ SEXT z :%⊢ w) (ExtRR f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v0 (
      eta (x :%∙ (y :%∙ SEXT z) :%⊢ w) f `app` pair v0 (pair v1 v3))))))))
eta ((x :%∙ y) :%∙ SEXT z :%⊢ w) (ExtLR f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v0 (
      eta ((x :%∙ SEXT z) :%∙ y :%⊢ w) f `app` pair (pair v0 v3) v1)))))))
eta (SEXT z :%∙ (y :%∙ x) :%⊢ w) (ExtLL f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta ((SEXT z :%∙ y) :%∙ x :%⊢ w) f `app` pair (pair v2 v0) v1)))))))
eta (SEXT z :%∙ (y :%∙ x) :%⊢ w) (ExtRL f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta (y :%∙ (SEXT z :%∙ x) :%⊢ w) f `app` pair v0 (pair v2 v1))))))))

-- Infixation
eta (x :%∙ (y :%∙ SIFX z) :%⊢ w) (IfxRR f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta ((x :%∙ y) :%∙ SIFX z :%⊢ w) f `app` pair (pair v2 v0) v1)))))))
eta ((x :%∙ SIFX z) :%∙ y :%⊢ w) (IfxLR f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v0 (
      eta ((x :%∙ y) :%∙ SIFX z :%⊢ w) f `app` pair (pair v0 v3) v1)))))))
eta ((SIFX z :%∙ y) :%∙ x :%⊢ w) (IfxLL f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v0 (
      eta (SIFX z :%∙ (y :%∙ x) :%⊢ w) f `app` pair v0 (pair v1 v3))))))))
eta (y :%∙ (SIFX z :%∙ x) :%⊢ w) (IfxRL f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta (SIFX z :%∙ (y :%∙ x) :%⊢ w) f `app` pair v0 (pair v2 v1))))))))

-- Right units
eta (SStI (SUnitR k a) :%⊢ y) (UnitRL  f) =
  withH a (withHO y (abs (eta (SPROD k (SStI a) (SUNIT k) :%⊢ y) f `app` pair v0 unit)))
eta (SPROD _ x (SUNIT _) :%⊢> SUnitR _ b) (UnitRR  f) =
  withH b (withHI x (abs (caseof v0 (eta (x :%⊢> b) f `app` v0))))
eta (SPROD _ x (SUNIT _) :%⊢ y) (UnitRI  f) =
  withHI x (withHO y (abs (caseof v0 (eta (x :%⊢ y) f `app` v0))))

-- Quantifier raising
eta (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w) (DnB f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta (x :%∙ (y :%∘ z) :%⊢ w) f `app` pair (proj2 v0) (pair v2 v1))))))))
eta (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w) (DnC f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta ((x :%∘ y) :%∙ z :%⊢ w) f `app` pair (pair v2 (proj2 v0)) v1)))))))
eta (x :%∙ (y :%∘ z) :%⊢ w)          (UpB f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v1 (
      eta (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w) f `app` pair v0 (pair (pair unit v2) v1))))))))
eta ((x :%∘ y) :%∙ z :%⊢ w)          (UpC f) =
  withHI x (withHI y (withHI z (withHO w (
    abs (caseof v0 (caseof v0 (
      eta (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w) f `app` pair v0 (pair (pair unit v1) v3))))))))


-- -}
-- -}
-- -}
-- -}
-- -}
