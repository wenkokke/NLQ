{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies #-}
module NLIBC.Syntax.Backward where


import           NLIBC.Syntax.Base
import           Control.Applicative (Alternative(empty,(<|>)))
import           Control.Monad (msum,MonadPlus(..))
import           Control.Monad.State.Strict (StateT,get,put,evalStateT)
import qualified Data.List.Ordered as OL
import qualified Data.List as L
import           Data.Maybe (isJust,fromJust,maybeToList)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,promoteOnly,singletons)
import           Unsafe.Coerce (unsafeCoerce)


-- * Proof search

find :: SSequent s -> Maybe (Syn s)
find ss = evalStateT (search ss) S.empty

findAll :: SSequent s -> [Syn s]
findAll ss = evalStateT (search ss) S.empty


-- * Backward-Chaining Proof Search (with loop checking)

type Search m a = (MonadPlus m) => StateT (Set Sequent) m a

search :: SSequent s -> Search m (Syn s)
search ss = do
  visited <- get
  put (S.insert (fromSing ss) visited)
  msum (fmap ($ ss) nl)
  where
    nl = concat
          [ [ax]
          , [withL1,withL2,withR]
          , [impRL,impRR,impLL,impLR,res11,res12,res13,res14]
          , [diaL,diaR,boxL,boxR,res21,res22]
          , [extLL,extLR,extRL,extRR]
          , [ifxLL,ifxLR,ifxRL,ifxRR]
          , [qrR',qrL']
          ]

    loop :: SSequent s -> Search m (Syn s)
    loop ss = do
      let s = fromSing ss
      visited <- get
      if (S.member s visited)
        then empty
        else put (S.insert s visited) >> search ss

    prog :: SSequent s -> Search m (Syn s)
    prog ss = do put (S.empty); search ss

    ax :: SSequent s -> Search m (Syn s)
    ax  (SStI a1 :%⊢ SStO a2) =
      case a1 %~ a2 of { Proved Refl -> pure Ax; _ -> empty }
    ax  _                     = empty

    withL1,withL2,withR :: SSequent s -> Search m (Syn s)
    withL1 (a1 :%& a2 :%<⊢ y) = WithL1 <$> prog (a1 :%<⊢ y)
    withL1 _                  = empty
    withL2 (a1 :%& a2 :%<⊢ y) = WithL2 <$> prog (a2 :%<⊢ y)
    withL2 _                  = empty
    withR  (x :%⊢> b1 :%& b2) = WithR  <$> prog (x :%⊢> b1) <*> prog (x :%⊢> b2)
    withR  _                  = empty

    impRL,impRR,impLL,impLR,res11,res12,res13,res14 :: SSequent s -> Search m (Syn s)
    impRL (SImpR k1 a b :%<⊢ SIMPR k2 x y) = case k1 %~ k2 of
          Proved Refl                     -> ImpRL <$> prog (x :%⊢> a) <*> prog (b :%<⊢ y)
          _                               -> empty
    impRL _                                = empty
    impRR (x :%⊢ SStO (SImpR k a b))       = ImpRR <$> prog (x :%⊢ SIMPR k (SStI a) (SStO b))
    impRR _                                = empty
    impLL (SImpL k1 b a :%<⊢ SIMPL k2 y x) = case k1 %~ k2 of
          Proved Refl                     -> ImpLL <$> prog (x :%⊢> a) <*> prog (b :%<⊢ y)
          _                               -> empty
    impLL _                                = empty
    impLR (x :%⊢ SStO (SImpL k b a))       = ImpLR <$> prog (x :%⊢ SIMPL k (SStO b) (SStI a))
    impLR _                                = empty
    res11 (SPROD k x y :%⊢ z)              = Res11 <$> loop (y :%⊢ SIMPR k x z)
    res11 _                                = empty
    res12 (y :%⊢ SIMPR k x z)              = Res12 <$> loop (SPROD k x y :%⊢ z)
    res12 _                                = empty
    res13 (SPROD k x y :%⊢ z)              = Res13 <$> loop (x :%⊢ SIMPL k z y)
    res13 _                                = empty
    res14 (x :%⊢ SIMPL k z y)              = Res14 <$> loop (SPROD k x y :%⊢ z)
    res14 _                                = empty

    diaL, diaR, boxL, boxR, res21, res22 :: SSequent s -> Search m (Syn s)
    diaL  (SStI (SDia k a) :%⊢ y)    = DiaL <$> prog (SDIA k (SStI a) :%⊢ y)
    diaL  _                          = empty
    diaR  (SDIA k1 x :%⊢> SDia k2 b) = case k1 %~ k2 of
          Proved Refl               -> DiaR <$> prog (x :%⊢> b)
          _                         -> empty
    diaR  _                          = empty
    boxL  (SBox k1 a :%<⊢ SBOX k2 y) = case k1 %~ k2 of
          Proved Refl               -> BoxL <$> prog (a :%<⊢ y)
          _                         -> empty
    boxL  _                          = empty
    boxR  (x :%⊢ SStO (SBox k a))    = BoxR <$> prog (x :%⊢ SBOX k (SStO a))
    boxR  _                          = empty
    res21 (SDIA k x :%⊢ y)           = Res21 <$> loop (x :%⊢ SBOX k y)
    res21 _                          = empty
    res22 (x :%⊢ SBOX k y)           = Res22 <$> loop (SDIA k x :%⊢ y)
    res22 _                          = empty

    ifxRR,ifxLR,ifxLL,ifxRL :: SSequent s -> Search m (Syn s)
    ifxRR (x :%∙ (y :%∙ SIFX z) :%⊢ w) = IfxRR <$> loop ((x :%∙ y) :%∙ SIFX z :%⊢ w)
    ifxRR _                            = empty
    ifxLR ((x :%∙ SIFX z) :%∙ y :%⊢ w) = IfxLR <$> loop ((x :%∙ y) :%∙ SIFX z :%⊢ w)
    ifxLR _                            = empty
    ifxLL ((SIFX z :%∙ y) :%∙ x :%⊢ w) = IfxLL <$> loop (SIFX z :%∙ (y :%∙ x) :%⊢ w)
    ifxLL _                            = empty
    ifxRL (y :%∙ (SIFX z :%∙ x) :%⊢ w) = IfxRL <$> loop (SIFX z :%∙ (y :%∙ x) :%⊢ w)
    ifxRL _                            = empty

    extRR,extLR,extLL,extRL :: SSequent s -> Search m (Syn s)
    extRR ((x :%∙ y) :%∙ SEXT z :%⊢ w) = ExtRR <$> loop (x :%∙ (y :%∙ SEXT z) :%⊢ w)
    extRR _                            = empty
    extLR ((x :%∙ y) :%∙ SEXT z :%⊢ w) = ExtLR <$> loop ((x :%∙ SEXT z) :%∙ y :%⊢ w)
    extLR _                            = empty
    extLL (SEXT z :%∙ (y :%∙ x) :%⊢ w) = ExtLL <$> loop ((SEXT z :%∙ y) :%∙ x :%⊢ w)
    extLL _                            = empty
    extRL (SEXT z :%∙ (y :%∙ x) :%⊢ w) = ExtRL <$> loop (y :%∙ (SEXT z :%∙ x) :%⊢ w)
    extRL _                            = empty

    {-
    unitL,unitR,unitI :: SSequent s -> Search m (Syn s)
    unitL (SStI (SUnitR k a) :%⊢ y)                = UnitRL <$> prog (SPROD k (SStI a) (SUNIT k) :%⊢ y)
    unitL _                                        = empty
    unitR (SPROD k1 x (SUNIT k2) :%⊢> SUnitR k3 b) = case (k1 %~ k2,k1 %~ k3) of
          (Proved Refl,Proved Refl)               -> UnitRR <$> prog (x :%⊢> b)
          _                                       -> empty
    unitR _                                        = empty
    unitI (SPROD k1 x (SUNIT k2) :%⊢ y)            = case k1 %~ k2 of
          Proved Refl                             -> UnitRI <$> prog (x :%⊢ y)
          _                                       -> empty
    unitI _                                        = empty
    -}

    {-
    dnB, dnC, upB, upC :: SSequent s -> Search m (Syn s)
    upB (x :%∙ (y :%∘ z) :%⊢ w)          = UpB <$> loop (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w)
    upB _                                = empty
    dnB (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w) = DnB <$> loop (x :%∙ (y :%∘ z) :%⊢ w)
    dnB _                                = empty
    upC ((x :%∘ y) :%∙ z :%⊢ w)          = UpC <$> loop (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w)
    upC _                                = empty
    dnC (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w) = DnC <$> loop ((x :%∘ y) :%∙ z :%⊢ w)
    dnC _                                = empty
    -}

    qrL',qrR' :: SSequent s -> Search m (Syn s)
    qrL' (x :%⊢ y)              = msum (app <$> sFocus x)
      where
        app (Focus x (SStI (SQR (c :%⇦ b))) Refl)
                                = qrL x <$> prog (sTrace x :%⊢> b) <*> prog (c :%<⊢ y)
        app _                   = empty
    qrL' _                      = empty
    qrR' (x :%⊢ SStO (a :%⇨ b)) = msum (maybeToList (app <$> sFollow x))
      where
        app (Trail x Refl)      = qrR x <$> prog (sPlug x (SStI a) :%⊢ SStO b)
    qrR' _                      = empty
