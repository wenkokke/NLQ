{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies,
    ViewPatterns, ScopedTypeVariables #-}
module NLIBC.Syntax.Base where


import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TH (promote,promoteOnly,singletons)
import Unsafe.Coerce (unsafeCoerce)


singletons [d|

  data Atom :: * where
    S   :: Atom
    N   :: Atom
    NP  :: Atom
    PP  :: Atom
    INF :: Atom
    deriving (Eq,Show)

  data Kind :: * where
    KSol :: Kind
    KHol :: Kind
    KRes :: Kind
    KIfx :: Kind
    KExt :: Kind
    deriving (Eq,Show)

  data Type :: * where
    El    :: Atom -> Type
    Dia   :: Kind -> Type -> Type
    Box   :: Kind -> Type -> Type
    UnitR :: Kind -> Type -> Type
    (:&)  :: Type -> Type -> Type
    ImpR  :: Kind -> Type -> Type -> Type
    ImpL  :: Kind -> Type -> Type -> Type
    deriving (Show,Eq)

  data StructI :: * where
    StI  :: Type -> StructI
    DIA  :: Kind -> StructI -> StructI
    B    :: StructI
    C    :: StructI
    UNIT :: Kind -> StructI
    PROD :: Kind -> StructI -> StructI -> StructI
    deriving (Eq,Show)

  data StructO :: * where
    StO  :: Type -> StructO
    BOX  :: Kind -> StructO -> StructO
    IMPR :: Kind -> StructI -> StructO -> StructO
    IMPL :: Kind -> StructO -> StructI -> StructO
    deriving (Eq,Show)

  data Sequent :: * where
    (:⊢)  :: StructI -> StructO -> Sequent
    (:<⊢) :: Type    -> StructO -> Sequent
    (:⊢>) :: StructI -> Type    -> Sequent
    deriving (Eq,Show)

  data Context :: * where
    HOLE  :: Context
    (:<∙) :: Context -> StructI -> Context
    (:∙>) :: StructI -> Context -> Context

  |]

infix  1 :⊢, :⊢>, :<⊢, :%⊢, :%⊢>, :%<⊢
infixr 3 :<∙, :∙>
infixr 5 :&, :%&

promote [d|

  plug :: Context -> StructI -> StructI
  plug HOLE      z = z
  plug (x :<∙ y) z = PROD KSol (plug x z) y
  plug (x :∙> y) z = PROD KSol x (plug y z)

  trace :: Context -> StructI
  trace HOLE      = UNIT KHol
  trace (x :∙> y) = PROD KSol (PROD KSol B x) (trace y)
  trace (x :<∙ y) = PROD KSol (PROD KSol C (trace x)) y

  |]


deriving instance Ord Atom
deriving instance Ord Kind
deriving instance Ord Type
deriving instance Ord StructI
deriving instance Ord StructO
deriving instance Ord Sequent
deriving instance Bounded Kind
deriving instance Enum Kind

kinds :: [Kind]
kinds = [minBound..maxBound]


infix  1 ⊢
infixr 3 ∙

class Product a b c | a b -> c where
  (∙) :: a -> b -> c
instance Product (SStructI x) (SStructI y) (SStructI (x :∙ y)) where
  x ∙ y = x :%∙ y
instance Product (SType a) (SStructI y) (SStructI (StI a :∙ y)) where
  a ∙ y = SStI a :%∙ y
instance Product (SStructI x) (SType b) (SStructI (x :∙ StI b)) where
  x ∙ b = x :%∙ SStI b
instance Product (SType a) (SType b) (SStructI (StI a :∙ StI b)) where
  a ∙ b = SStI a :%∙ SStI b

class Turnstile a b c | a b -> c where
  (⊢) :: a -> b -> c
instance Turnstile (SStructI x) (SStructO y) (SSequent (x :⊢ y)) where
  x ⊢ y = x :%⊢ y
instance Turnstile (SType a) (SStructO y) (SSequent (StI a :⊢ y)) where
  a ⊢ y = SStI a :%⊢ y
instance Turnstile (SStructI x) (SType b) (SSequent (x :⊢ StO b)) where
  x ⊢ b = x :%⊢ SStO b
instance Turnstile (SType a) (SType b) (SSequent (StI a :⊢ StO b)) where
  a ⊢ b = SStI a :%⊢ SStO b



infixr 3 :∙, :%∙
infixr 7 :→, :%→
infixl 7 :←, :%←

type    x  :∙ y =  PROD  KSol  x y
pattern x  :∙ y =  PROD  KSol  x y
pattern x :%∙ y = SPROD SKSol  x y
type    x  :→ y =  ImpR  KSol  x y
pattern x  :→ y =  ImpR  KSol  x y
pattern x :%→ y = SImpR SKSol  x y
type    y  :← x =  ImpL  KSol  y x
pattern y  :← x =  ImpL  KSol  y x
pattern y :%← x = SImpL SKSol  y x

type     QR x =  UnitR  KHol x
pattern  QR x =  UnitR  KHol x
pattern SQR x = SUnitR SKHol x

type     I =  UNIT  KHol
pattern  I =  UNIT  KHol
pattern SI = SUNIT SKHol

type    x  :∘ y =  PROD  KHol x y
pattern x  :∘ y =  PROD  KHol x y
pattern x :%∘ y = SPROD SKHol x y
type    x  :⇨ y =  ImpR  KHol x y
pattern x  :⇨ y =  ImpR  KHol x y
pattern x :%⇨ y = SImpR SKHol x y
type    y  :⇦ x =  ImpL  KHol y x
pattern y  :⇦ x =  ImpL  KHol y x
pattern y :%⇦ x = SImpL SKHol y x

type     Q a b c =  QR (c  :⇦ (a  :⇨ b))
pattern  Q a b c =  QR (c  :⇦ (a  :⇨ b))
pattern SQ a b c = SQR (c :%⇦ (a :%⇨ b))

type     Res a =  Dia  KRes a
pattern  Res a =  Dia  KRes a
pattern SRes a = SDia SKRes a
type     RES x =  DIA  KRes x
pattern  RES x =  DIA  KRes x
pattern SRES x = SDIA SKRes x

type     Ifx a =  Dia  KIfx ( Box  KIfx a)
pattern  Ifx a =  Dia  KIfx ( Box  KIfx a)
pattern SIfx a = SDia SKIfx (SBox SKIfx a)
type     IFX x =  DIA  KIfx x
pattern  IFX x =  DIA  KIfx x
pattern SIFX x = SDIA SKIfx x

type     Ext a =  Dia  KExt ( Box  KExt a)
pattern  Ext a =  Dia  KExt ( Box  KExt a)
pattern SExt a = SDia SKExt (SBox SKExt a)
type     EXT x =  DIA  KExt x
pattern  EXT x =  DIA  KExt x
pattern SEXT x = SDIA SKExt x

type    a  :⇃ b = ( Ext a)  :→ b
pattern a  :⇃ b = ( Ext a)  :→ b
pattern a :%⇃ b = (SExt a) :%→ b
type    b  :⇂ a = b  :←  Ext a
pattern b  :⇂ a = b  :←  Ext a
pattern b :%⇂ a = b :%← SExt a

type    a  :↿ b =  Ifx (a  :→ b)
pattern a  :↿ b =  Ifx (a  :→ b)
pattern a :%↿ b = SIfx (a :%→ b)
type    b  :↾ a =  Ifx (b  :← a)
pattern b  :↾ a =  Ifx (b  :← a)
pattern b :%↾ a = SIfx (b :%← a)



-- * Operations on Types and Structures

data Focus (z :: StructI) :: * where
     Focus :: SContext x -> SStructI y -> Plug x y :~: z -> Focus z

data Trail (z :: StructI) :: * where
     Trail :: SContext x -> Trace x :~: z -> Trail z

sPlug :: SContext x -> SStructI z -> SStructI (Plug x z)
sPlug SHOLE      z = z
sPlug (x :%<∙ y) z = SPROD SKSol (sPlug x z) y
sPlug (x :%∙> y) z = SPROD SKSol x (sPlug y z)

sTrace :: SContext x -> SStructI (Trace x)
sTrace SHOLE      = SI
sTrace (x :%∙> y) = SPROD SKSol (SPROD SKSol SB x) (sTrace y)
sTrace (x :%<∙ y) = SPROD SKSol (SPROD SKSol SC (sTrace x)) y

sFocus :: SStructI x -> [Focus x]
sFocus x = Focus SHOLE x Refl : sFocus' x
  where
    sFocus' :: SStructI x -> [Focus x]
    sFocus' (x :%∙ y) = (inl <$> sFocus x) ++ (inr <$> sFocus y)
      where
        inl (Focus x z Refl) = Focus (x :%<∙ y) z Refl
        inr (Focus y z Refl) = Focus (x :%∙> y) z Refl
    sFocus' x         = []

sFollow :: SStructI x -> Maybe (Trail x)
sFollow  SI                = Just (Trail SHOLE Refl)
sFollow ((SC :%∙ x) :%∙ y) = case sFollow x of
  Just (Trail x Refl)     -> Just (Trail (x :%<∙ y) Refl)
  _                       -> Nothing
sFollow ((SB :%∙ x) :%∙ y) = case sFollow y of
  Just (Trail y Refl)     -> Just (Trail (x :%∙> y) Refl)
  _                       -> Nothing
sFollow _                  = Nothing



-- * Positive and Negative Types

data Pos :: Type -> * where
  Pos_Dia    :: Pos (Dia k a)
  Pos_UnitR  :: Pos (UnitR k a)

data Neg :: Type -> * where
  Neg_El     :: Neg (El a)
  Neg_Box    :: Neg (Box k a)
  Neg_With   :: Neg (a1 :& a2)
  Neg_ImpR   :: Neg (ImpR k a b)
  Neg_ImpL   :: Neg (ImpL k b a)

pol :: SType a -> Either (Pos a) (Neg a)
pol (SEl a)       = Right Neg_El
pol (_ :%& _)     = Right Neg_With
pol (SDia _ _)    = Left  Pos_Dia
pol (SBox _ _)    = Right Neg_Box
pol (SUnitR _ _)  = Left  Pos_UnitR
pol (SImpR _ _ _) = Right Neg_ImpR
pol (SImpL _ _ _) = Right Neg_ImpL



-- * Instances

instance Show (SAtom    s) where show = show . fromSing
instance Show (SKind    s) where show = show . fromSing
instance Show (SType    s) where show = show . fromSing
instance Show (SStructI s) where show = show . fromSing

instance Eq (SAtom    s) where x == y = fromSing x == fromSing y
instance Eq (SKind    s) where x == y = fromSing x == fromSing y
instance Eq (SType    s) where x == y = fromSing x == fromSing y
instance Eq (SStructI s) where x == y = fromSing x == fromSing y

instance Ord (SAtom    s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SKind    s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SType    s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SStructI s) where compare x y = compare (fromSing x) (fromSing y)


type family ToList (x :: StructI) :: [StructI] where
  ToList (StI  a    ) = (StI a ': '[])
  ToList (DIA  k x  ) = ToList x
  ToList (PROD k x y) = ToList x :++ ToList y


sToList :: SStructI x -> Maybe (SList (ToList x))
sToList x@(SStI  a)     = Just (SCons x SNil)
sToList   (SDIA  k x)   = sToList x
sToList   (SPROD k x y) = (%:++) <$> sToList x <*> sToList y
sToList   _             = Nothing


-- * Proofs

data Syn :: Sequent -> * where
  AxR    :: Pos b -> Syn (StI b :⊢> b)
  AxL    :: Neg a -> Syn (a :<⊢ StO a)
  UnfR   :: Neg b -> Syn (x :⊢ StO b) -> Syn (x :⊢> b)
  UnfL   :: Pos a -> Syn (StI a :⊢ y) -> Syn (a :<⊢ y)
  FocR   :: Pos b -> Syn (x :⊢> b) -> Syn (x :⊢ StO b)
  FocL   :: Neg a -> Syn (a :<⊢ y) -> Syn (StI a :⊢ y)

  WithL1 :: Syn (a1 :<⊢ y) -> Syn (a1 :& a2 :<⊢ y)
  WithL2 :: Syn (a2 :<⊢ y) -> Syn (a1 :& a2 :<⊢ y)
  WithR  :: Syn (x :⊢> b1) -> Syn (x :⊢> b2) -> Syn (x :⊢> b1 :& b2)

  ImpRL  :: Syn (x :⊢> a) -> Syn (b :<⊢ y) -> Syn (ImpR k a b :<⊢ IMPR k x y)
  ImpRR  :: Syn (x :⊢ IMPR k (StI a) (StO b)) -> Syn (x :⊢ StO (ImpR k a b))
  ImpLL  :: Syn (x :⊢> a) -> Syn (b :<⊢ y) -> Syn (ImpL k b a :<⊢ IMPL k y x)
  ImpLR  :: Syn (x :⊢ IMPL k (StO b) (StI a)) -> Syn (x :⊢ StO (ImpL k b a))
  Res11  :: Syn (y :⊢ IMPR k x z) -> Syn (PROD k x y :⊢ z)
  Res12  :: Syn (PROD k x y :⊢ z) -> Syn (y :⊢ IMPR k x z)
  Res13  :: Syn (x :⊢ IMPL k z y) -> Syn (PROD k x y :⊢ z)
  Res14  :: Syn (PROD k x y :⊢ z) -> Syn (x :⊢ IMPL k z y)

  DiaL   :: Syn (DIA k (StI a) :⊢ y) -> Syn (StI (Dia k a) :⊢ y)
  DiaR   :: Syn (x :⊢> b) -> Syn (DIA k x :⊢> Dia k b)
  BoxL   :: Syn (a :<⊢ y) -> Syn (Box k a :<⊢ BOX k y)
  BoxR   :: Syn (x :⊢ BOX k (StO b)) -> Syn (x :⊢ StO (Box k b))
  Res21  :: Syn (x :⊢ BOX k y) -> Syn (DIA k x :⊢ y)
  Res22  :: Syn (DIA k x :⊢ y) -> Syn (x :⊢ BOX k y)

  IfxRR   :: Syn ((x :∙ y) :∙ IFX z :⊢ w) -> Syn (x :∙ (y :∙ IFX z) :⊢ w)
  IfxLR   :: Syn ((x :∙ y) :∙ IFX z :⊢ w) -> Syn ((x :∙ IFX z) :∙ y :⊢ w)
  IfxLL   :: Syn (IFX z :∙ (y :∙ x) :⊢ w) -> Syn ((IFX z :∙ y) :∙ x :⊢ w)
  IfxRL   :: Syn (IFX z :∙ (y :∙ x) :⊢ w) -> Syn (y :∙ (IFX z :∙ x) :⊢ w)

  ExtRR   :: Syn (x :∙ (y :∙ EXT z) :⊢ w) -> Syn ((x :∙ y) :∙ EXT z :⊢ w)
  ExtLR   :: Syn ((x :∙ EXT z) :∙ y :⊢ w) -> Syn ((x :∙ y) :∙ EXT z :⊢ w)
  ExtLL   :: Syn ((EXT z :∙ y) :∙ x :⊢ w) -> Syn (EXT z :∙ (y :∙ x) :⊢ w)
  ExtRL   :: Syn (y :∙ (EXT z :∙ x) :⊢ w) -> Syn (EXT z :∙ (y :∙ x) :⊢ w)

  UnitRL :: Syn (PROD k (StI a) (UNIT k) :⊢ y) -> Syn (StI (UnitR k a) :⊢ y)
  UnitRR :: Syn (x :⊢> b) -> Syn (PROD k x (UNIT k) :⊢> UnitR k b)
  UnitRI :: Syn (x :⊢ y) -> Syn (PROD k x (UNIT k) :⊢ y)

  DnB    :: Syn (x :∙ (y :∘ z) :⊢ w) -> Syn (y :∘ ((B :∙ x) :∙ z) :⊢ w)
  UpB    :: Syn (y :∘ ((B :∙ x) :∙ z) :⊢ w) -> Syn (x :∙ (y :∘ z) :⊢ w)
  DnC    :: Syn ((x :∘ y) :∙ z :⊢ w) -> Syn (x :∘ ((C :∙ y) :∙ z) :⊢ w)
  UpC    :: Syn (x :∘ ((C :∙ y) :∙ z) :⊢ w) -> Syn ((x :∘ y) :∙ z :⊢ w)


instance Show (SSequent s) where
  show ss = show (fromSing ss)

deriving instance Eq   (Pos s)
deriving instance Eq   (Neg s)
deriving instance Eq   (Syn s)
deriving instance Ord  (Pos s)
deriving instance Ord  (Neg s)
deriving instance Show (Pos s)
deriving instance Show (Neg s)
deriving instance Show (Syn s)


-- * Quantifier Raising


up :: SContext x -> Syn (Plug x y :⊢ z) -> Syn (y :∘ Trace x :⊢ z)
up SHOLE      f = UnitRI f
up (x :%<∙ y) f = DnC (Res13 (unsafeCoerce (up x (Res14 (unsafeCoerce f)))))
up (x :%∙> y) f = DnB (Res11 (unsafeCoerce (up y (Res12 (unsafeCoerce f)))))

down :: SContext x -> Syn (StI a :∘ Trace x :⊢ z) -> Syn (Plug x (StI (QR a)) :⊢ z)
down x f = unsafeCoerce (init x (unsafeCoerce (move x f)))
  where
    init :: SContext x -> Syn (Plug x (StI a :∘ I) :⊢ y) -> Syn (Plug x (StI (QR a)) :⊢ y)
    init SHOLE      f = UnitRL f
    init (x :%<∙ y) f = Res13 (unsafeCoerce (init x (Res14 (unsafeCoerce f))))
    init (x :%∙> y) f = Res11 (unsafeCoerce (init y (Res12 (unsafeCoerce f))))
    move :: SContext x -> Syn (y :∘ Trace x :⊢ z) -> Syn (Plug x (y :∘ I) :⊢ z)
    move SHOLE      f = f
    move (x :%<∙ y) f = Res13 (unsafeCoerce (move x (Res14 (UpC (unsafeCoerce f)))))
    move (x :%∙> y) f = Res11 (unsafeCoerce (move y (Res12 (UpB (unsafeCoerce f)))))

qrL :: SContext x
    -> Syn (Trace x :⊢> b)
    -> Syn (c :<⊢ y)
    -> Syn (Plug x (StI (QR (c :⇦ b))) :⊢ y)
qrL x f g = unsafeCoerce (down x (Res13 (FocL Neg_ImpL (ImpLL f g))))

qrR :: SContext x
    -> Syn (Plug x (StI a) :⊢ StO b)
    -> Syn (Trace x :⊢ StO (a :⇨ b))
qrR x f = ImpRR (Res12 (up x f))


-- * Forgetful version of `Syn` type for easy deriving of Ord

-- Yes, this is kinda ugly. But writing out an Ord instance is a pain,
-- and I'll do anything I can to avoid having to do that. Plus, that
-- would just hugely clutter up the file. And since this is pretty
-- much macro written, it has a bigger chance to be correct. ^^

data USyn
   = UAxR              | UAxL
   | UUnfR   USyn      | UUnfL   USyn | UFocR   USyn      | UFocL USyn
   | UWithL1 USyn      | UWithL2 USyn | UWithR  USyn USyn
   | UImpRL  USyn USyn | UImpRR  USyn | UImpLL  USyn USyn | UImpLR USyn
   | URes11  USyn      | URes12  USyn | URes13  USyn      | URes14 USyn
   | UDiaL   USyn      | UDiaR   USyn | UBoxL   USyn      | UBoxR USyn
   | URes21  USyn      | URes22  USyn
   | UIfxRR  USyn      | UIfxLR  USyn | UIfxLL  USyn      | UIfxRL USyn
   | UExtRR  USyn      | UExtLR  USyn | UExtLL  USyn      | UExtRL USyn
   | UUnitRL USyn      | UUnitRR USyn | UUnitRI USyn
   | UDnB    USyn      | UUpB    USyn | UDnC    USyn      | UUpC USyn
   deriving (Eq,Ord)

forget :: Syn s -> USyn
forget (AxR  _)     = UAxR
forget (AxL  _)     = UAxL
forget (UnfR _ f)   = UUnfR   (forget f)
forget (UnfL _ f)   = UUnfL   (forget f)
forget (FocR _ f)   = UFocR   (forget f)
forget (FocL _ f)   = UFocL   (forget f)
forget (WithL1 f)   = UWithL1 (forget f)
forget (WithL2 f)   = UWithL2 (forget f)
forget (WithR  f g) = UWithR  (forget f) (forget g)
forget (ImpRL  f g) = UImpRL  (forget f) (forget g)
forget (ImpRR  f)   = UImpRR  (forget f)
forget (ImpLL  f g) = UImpLL  (forget f) (forget g)
forget (ImpLR  f)   = UImpLR  (forget f)
forget (Res11  f)   = URes11  (forget f)
forget (Res12  f)   = URes12  (forget f)
forget (Res13  f)   = URes13  (forget f)
forget (Res14  f)   = URes14  (forget f)
forget (DiaL   f)   = UDiaL   (forget f)
forget (DiaR   f)   = UDiaR   (forget f)
forget (BoxL   f)   = UBoxL   (forget f)
forget (BoxR   f)   = UBoxR   (forget f)
forget (Res21  f)   = URes21  (forget f)
forget (Res22  f)   = URes22  (forget f)
forget (IfxRR  f)   = UIfxRR  (forget f)
forget (IfxLR  f)   = UIfxLR  (forget f)
forget (IfxLL  f)   = UIfxLL  (forget f)
forget (IfxRL  f)   = UIfxRL  (forget f)
forget (ExtRR  f)   = UExtRR  (forget f)
forget (ExtLR  f)   = UExtLR  (forget f)
forget (ExtLL  f)   = UExtLL  (forget f)
forget (ExtRL  f)   = UExtRL  (forget f)
forget (UnitRL f)   = UUnitRL (forget f)
forget (UnitRR f)   = UUnitRR (forget f)
forget (UnitRI f)   = UUnitRI (forget f)
forget (DnB    f)   = UDnB    (forget f)
forget (UpB    f)   = UUpB    (forget f)
forget (DnC    f)   = UDnC    (forget f)
forget (UpC    f)   = UUpC    (forget f)

instance Ord (Syn s) where
  f `compare` g = forget f `compare` forget g
