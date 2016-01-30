{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies #-}
module NLQ.Syntax.Backward where


import           NLQ.Syntax.Base
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
          [ [axL,unfR,unfL,focR,focL]
          , [withL1,withL2,withR]
          , [impRL,impRR,impLL,impLR,resRP,resPR,resLP,resPL]
          , [diaL,diaR,boxL,boxR,resBD,resDB]
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

    axL, unfR, unfL, focR, focL :: SSequent s -> Search m (Syn s)
    axL  (SEl a :%<⊢ SStO (SEl b)) = case a %~ b of
       { Proved Refl -> pure (AxL Neg_El); _ -> empty }
    axL  _               = empty
    unfR (x :%⊢> b)      = case pol b of
       { Right p -> UnfR p <$> loop (x :%⊢ SStO b); _ -> empty }
    unfR  _              = empty
    unfL (a :%<⊢ y)      = case pol a of
       { Left  p -> UnfL p <$> loop (SStI a :%⊢ y); _ -> empty }
    unfL  _              = empty
    focR (x :%⊢ SStO b)  = case pol b of
       { Left  p -> FocR p <$> loop (x :%⊢> b); _ -> empty }
    focR  _              = empty
    focL (SStI a :%⊢ y)  = case pol a of
       { Right p -> FocL p <$> loop (a :%<⊢ y); _ -> empty }
    focL  _              = empty

    withL1,withL2,withR :: SSequent s -> Search m (Syn s)
    withL1 (SStI (a1 :%& a2) :%⊢ y) = WithL1 <$> prog (a1 :%<⊢ y)
    withL1 _                        = empty
    withL2 (SStI (a1 :%& a2) :%⊢ y) = WithL2 <$> prog (a2 :%<⊢ y)
    withL2 _                        = empty
    withR  (x :%⊢> b1 :%& b2)       = WithR  <$> prog (x :%⊢ SStO b1) <*> prog (x :%⊢ SStO b2)
    withR  _                        = empty

    impRL,impRR,impLL,impLR,resRP,resPR,resLP,resPL :: SSequent s -> Search m (Syn s)
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
    resRP (SPROD k x y :%⊢ z)              = ResRP <$> loop (y :%⊢ SIMPR k x z)
    resRP _                                = empty
    resPR (y :%⊢ SIMPR k x z)              = ResPR <$> loop (SPROD k x y :%⊢ z)
    resPR _                                = empty
    resLP (SPROD k x y :%⊢ z)              = ResLP <$> loop (x :%⊢ SIMPL k z y)
    resLP _                                = empty
    resPL (x :%⊢ SIMPL k z y)              = ResPL <$> loop (SPROD k x y :%⊢ z)
    resPL _                                = empty

    diaL, diaR, boxL, boxR, resBD, resDB :: SSequent s -> Search m (Syn s)
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
    resBD (SDIA k x :%⊢ y)           = ResBD <$> loop (x :%⊢ SBOX k y)
    resBD _                          = empty
    resDB (x :%⊢ SBOX k y)           = ResDB <$> loop (SDIA k x :%⊢ y)
    resDB _                          = empty

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

    qrL',qrR' :: SSequent s -> Search m (Syn s)
    qrL' (x :%⊢ y) = msum (app <$> sFocus x)
      where
        app (Focus k3 x (SStI (SUnitL (SQuan k1) (SImpR (SQuan k2) b c))) Refl)
          = case k1 %~ k2 of
            Proved Refl -> case k3 of
              SWeak     -> qrL k1 x <$> prog (sTrace k1 x :%⊢> b) <*> prog (c :%<⊢ y)
              SStrong   -> case k1 of
                SWeak   -> empty
                SStrong -> qrL k1 x <$> prog (sTrace k1 x :%⊢> b) <*> prog (c :%<⊢ y)
            _           -> empty
        app _   = empty
    qrL'    _   = empty

    qrR' (x :%⊢ SStO (SImpL (SQuan k1) b a)) = msum (maybeToList (app <$> sFollow x))
      where
        app (Trail k2 x Refl) = case k1 %~ k2 of
          Proved Refl -> qrR k1 x <$> prog (sPlug x (SStI a) :%⊢ SStO b)
          _           -> empty
    qrR'  _            = empty
