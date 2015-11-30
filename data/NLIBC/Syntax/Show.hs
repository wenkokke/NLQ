{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
module NLIBC.Syntax.Show where


import NLIBC.Syntax.Base
import NLIBC.Syntax.Backward
import Data.Singletons.Prelude


lin :: SSequent s -> Syn s -> [(String, Sequent)]
lin ss@(SStI b1 :%⊢> b2)                (AxR  _)     = ("AxR"    , fromSing ss) : []
lin ss@(a1 :%<⊢ SStO a2)                (AxL  _)     = ("AxL"    , fromSing ss) : []
lin ss@(x :%⊢> b)                       (UnfR _ f)   = ("UnfR"   , fromSing ss) : lin (x :%⊢ SStO b) f
lin ss@(a :%<⊢ y)                       (UnfL _ f)   = ("UnfL"   , fromSing ss) : lin (SStI a :%⊢ y) f
lin ss@(x :%⊢ SStO b)                   (FocR _ f)   = ("FocR"   , fromSing ss) : lin (x :%⊢> b) f
lin ss@(SStI a :%⊢ y)                   (FocL _ f)   = ("FocL"   , fromSing ss) : lin (a :%<⊢ y) f
lin ss@(a1 :%& a2 :%<⊢ y)               (WithL1 f)   = ("WithL1" , fromSing ss) : lin (a1 :%<⊢ y) f
lin ss@(a1 :%& a2 :%<⊢ y)               (WithL2 f)   = ("WithL2" , fromSing ss) : lin (a2 :%<⊢ y) f
lin ss@(x :%⊢> b1 :%& b2)               (WithR  f g) = ("WithR"  , fromSing ss) : lin (x :%⊢> b1) f ++ lin (x :%⊢> b2) g
lin ss@(SImpR _ a b :%<⊢ SIMPR _ x y)   (ImpRL  f g) = ("ImpRL"  , fromSing ss) : lin (x :%⊢> a) f ++ lin (b :%<⊢ y) g
lin ss@(x :%⊢ SStO (SImpR k a b))       (ImpRR  f)   = ("ImpRR"  , fromSing ss) : lin (x :%⊢ SIMPR k (SStI a) (SStO b)) f
lin ss@(SImpL _ b a :%<⊢ SIMPL _ y x)   (ImpLL  f g) = ("ImpLL"  , fromSing ss) : lin (x :%⊢> a) f ++ lin (b :%<⊢ y) g
lin ss@(x :%⊢ SStO (SImpL k b a))       (ImpLR  f)   = ("ImpLR"  , fromSing ss) : lin (x :%⊢ SIMPL k (SStO b) (SStI a)) f
lin ss@(SPROD k x y :%⊢ z)              (Res11  f)   = ("Res11"  , fromSing ss) : lin (y :%⊢ SIMPR k x z) f
lin ss@(y :%⊢ SIMPR k x z)              (Res12  f)   = ("Res12"  , fromSing ss) : lin (SPROD k x y :%⊢ z) f
lin ss@(SPROD k x y :%⊢ z)              (Res13  f)   = ("Res13"  , fromSing ss) : lin (x :%⊢ SIMPL k z y) f
lin ss@(x :%⊢ SIMPL k z y)              (Res14  f)   = ("Res14"  , fromSing ss) : lin (SPROD k x y :%⊢ z) f
lin ss@(SStI (SDia k a) :%⊢ y)          (DiaL   f)   = ("DiaL"   , fromSing ss) : lin (SDIA k (SStI a) :%⊢ y) f
lin ss@(SDIA _ x :%⊢> SDia _ b)         (DiaR   f)   = ("DiaR"   , fromSing ss) : lin (x :%⊢> b) f
lin ss@(SBox _ a :%<⊢ SBOX _ y)         (BoxL   f)   = ("BoxL"   , fromSing ss) : lin (a :%<⊢ y) f
lin ss@(x :%⊢ SStO (SBox k b))          (BoxR   f)   = ("BoxR"   , fromSing ss) : lin (x :%⊢ SBOX k (SStO b)) f
lin ss@(SDIA k x :%⊢ y)                 (Res21  f)   = ("Res21"  , fromSing ss) : lin (x :%⊢ SBOX k y) f
lin ss@(x :%⊢ SBOX k y)                 (Res22  f)   = ("Res22"  , fromSing ss) : lin (SDIA k x :%⊢ y) f
lin ss@(x :%∙ (y :%∙ SIFX z) :%⊢ w)     (IfxRR  f)   = ("IfxRR"  , fromSing ss) : lin ((x :%∙ y) :%∙ SIFX z :%⊢ w) f
lin ss@((x :%∙ SIFX z) :%∙ y :%⊢ w)     (IfxLR  f)   = ("IfxLR"  , fromSing ss) : lin ((x :%∙ y) :%∙ SIFX z :%⊢ w) f
lin ss@((SIFX z :%∙ y) :%∙ x :%⊢ w)     (IfxLL  f)   = ("IfxLL"  , fromSing ss) : lin (SIFX z :%∙ (y :%∙ x) :%⊢ w) f
lin ss@(y :%∙ (SIFX z :%∙ x) :%⊢ w)     (IfxRL  f)   = ("IfxRL"  , fromSing ss) : lin (SIFX z :%∙ (y :%∙ x) :%⊢ w) f
lin ss@((x :%∙ y) :%∙ SEXT z :%⊢ w)     (ExtRR  f)   = ("ExtRR"  , fromSing ss) : lin (x :%∙ (y :%∙ SEXT z) :%⊢ w) f
lin ss@((x :%∙ y) :%∙ SEXT z :%⊢ w)     (ExtLR  f)   = ("ExtLR"  , fromSing ss) : lin ((x :%∙ SEXT z) :%∙ y :%⊢ w) f
lin ss@(SEXT z :%∙ (y :%∙ x) :%⊢ w)     (ExtLL  f)   = ("ExtLL"  , fromSing ss) : lin ((SEXT z :%∙ y) :%∙ x :%⊢ w) f
lin ss@(SEXT z :%∙ (y :%∙ x) :%⊢ w)     (ExtRL  f)   = ("ExtRL"  , fromSing ss) : lin (y :%∙ (SEXT z :%∙ x) :%⊢ w) f
lin ss@(SStI (SUnitR k a) :%⊢ y)        (UnitRL f)   = ("UnitRL" , fromSing ss) : lin (SPROD k (SStI a) (SUNIT k) :%⊢ y) f
lin ss@(SPROD _ x _ :%⊢> SUnitR _ b)    (UnitRR f)   = ("UnitRR" , fromSing ss) : lin (x :%⊢> b) f
lin ss@(SPROD _ x _ :%⊢ y)              (UnitRI f)   = ("UnitRI" , fromSing ss) : lin (x :%⊢ y) f
lin ss@(y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w) (DnB    f)   = ("DnB"    , fromSing ss) : lin (x :%∙ (y :%∘ z) :%⊢ w) f
lin ss@(x :%∙ (y :%∘ z) :%⊢ w)          (UpB    f)   = ("UpB"    , fromSing ss) : lin (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w) f
lin ss@(x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w) (DnC    f)   = ("DnC"    , fromSing ss) : lin ((x :%∘ y) :%∙ z :%⊢ w) f
lin ss@((x :%∘ y) :%∙ z :%⊢ w)          (UpC    f)   = ("UpC"    , fromSing ss) : lin (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w) f

{-

-}
