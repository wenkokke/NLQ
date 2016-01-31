{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies,
    ViewPatterns, ScopedTypeVariables #-}
module NLQ.Syntax.Base where


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

  data Strength :: * where
    Strong :: Strength
    Weak   :: Strength
    deriving (Eq,Show)

  data Kind :: * where
    Solid  :: Kind
    Quan   :: Strength -> Kind
    Delim  :: Strength -> Kind
    Ifx :: Kind
    Ext :: Kind
    deriving (Eq,Show)

  data Type :: * where
    El    :: Atom -> Type
    Dia   :: Kind -> Type -> Type
    Box   :: Kind -> Type -> Type
    UnitL :: Kind -> Type -> Type
    (:&)  :: Type -> Type -> Type
    ImpR  :: Kind -> Type -> Type -> Type
    ImpL  :: Kind -> Type -> Type -> Type
    deriving (Show,Eq)

  data StructI :: * where
    StI  :: Type -> StructI
    DIA  :: Kind -> StructI -> StructI
    B    :: StructI
    C    :: StructI
    I'   :: StructI
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
    DelW1 :: Context -> Context
    (:<∙) :: Context -> StructI -> Context
    (:∙>) :: StructI -> Context -> Context
    deriving (Eq,Show)

  |]

infix  1 :⊢, :⊢>, :<⊢, :%⊢, :%⊢>, :%<⊢
infixr 3 :<∙, :∙>
infixr 5 :&, :%&

promote [d|

  plug :: Context -> StructI -> StructI
  plug HOLE      z = z
  plug (DelW1 x) z = DIA (Delim Weak) (plug x z)
  plug (x :<∙ y) z = PROD Solid (plug x z) y
  plug (x :∙> y) z = PROD Solid x (plug y z)

  trace :: Strength -> Context -> StructI
  trace k HOLE      = UNIT (Quan k)
  trace k (DelW1 x) = PROD Solid I' (DIA (Delim Weak) (trace k x))
  trace k (x :∙> y) = PROD Solid (PROD Solid B x) (trace k y)
  trace k (x :<∙ y) = PROD Solid (PROD Solid C (trace k x)) y

  |]


deriving instance Ord Atom
deriving instance Ord Strength
deriving instance Ord Kind
deriving instance Ord Type
deriving instance Ord StructI
deriving instance Ord StructO
deriving instance Ord Sequent

kinds :: [Kind]
kinds = [Solid,Quan Weak,Quan Strong,Delim Weak,Delim Strong,Ifx,Ext]

infixr 3 :∙, :%∙
infixr 7 :→, :%→
infixl 7 :←, :%←

type    x  :∙ y =  PROD  Solid  x y
pattern x  :∙ y =  PROD  Solid  x y
pattern x :%∙ y = SPROD SSolid  x y
type    x  :→ y =  ImpR  Solid  x y
pattern x  :→ y =  ImpR  Solid  x y
pattern x :%→ y = SImpR SSolid  x y
type    y  :← x =  ImpL  Solid  y x
pattern y  :← x =  ImpL  Solid  y x
pattern y :%← x = SImpL SSolid  y x

type     QLW x =  UnitL  (Quan Weak) x
pattern  QLW x =  UnitL  (Quan Weak) x
pattern SQLW x = SUnitL (SQuan SWeak) x

type     QLS x =  UnitL  (Quan Strong) x
pattern  QLS x =  UnitL  (Quan Strong) x
pattern SQLS x = SUnitL (SQuan SStrong) x

type    x  :∘ y =  PROD  (Quan  Weak) x y
pattern x  :∘ y =  PROD  (Quan  Weak) x y
pattern x :%∘ y = SPROD (SQuan SWeak) x y
type    x  :⇨ y =  ImpR  (Quan  Weak) x y
pattern x  :⇨ y =  ImpR  (Quan  Weak) x y
pattern x :%⇨ y = SImpR (SQuan SWeak) x y
type    y  :⇦ x =  ImpL  (Quan  Weak) y x
pattern y  :⇦ x =  ImpL  (Quan  Weak) y x
pattern y :%⇦ x = SImpL (SQuan SWeak) y x

type     DelW a =  Dia  (Delim  Weak) a
pattern  DelW a =  Dia  (Delim  Weak) a
pattern SDelW a = SDia (SDelim SWeak) a
type     DELW x =  DIA  (Delim  Weak) x
pattern  DELW x =  DIA  (Delim  Weak) x
pattern SDELW x = SDIA (SDelim SWeak) x

type     DelS a =  Dia  (Delim  Strong) a
pattern  DelS a =  Dia  (Delim  Strong) a
pattern SDelS a = SDia (SDelim SStrong) a
type     DELS x =  DIA  (Delim  Strong) x
pattern  DELS x =  DIA  (Delim  Strong) x
pattern SDELS x = SDIA (SDelim SStrong) x

type     IFX x =  DIA  Ifx x
pattern  IFX x =  DIA  Ifx x
pattern SIFX x = SDIA SIfx x
type     EXT x =  DIA  Ext x
pattern  EXT x =  DIA  Ext x
pattern SEXT x = SDIA SExt x

type    a  :⇃ b = ( Dia  Ext ( Box  Ext a))  :→ b
pattern a  :⇃ b = ( Dia  Ext ( Box  Ext a))  :→ b
pattern a :%⇃ b = (SDia SExt (SBox SExt a)) :%→ b
type    b  :⇂ a = b  :←  Dia  Ext ( Box  Ext a)
pattern b  :⇂ a = b  :←  Dia  Ext ( Box  Ext a)
pattern b :%⇂ a = b :%← SDia SExt (SBox SExt a)

type    a  :↿ b =  Dia  Ifx ( Box  Ifx (a  :→ b))
pattern a  :↿ b =  Dia  Ifx ( Box  Ifx (a  :→ b))
pattern a :%↿ b = SDia SIfx (SBox SIfx (a :%→ b))
type    b  :↾ a =  Dia  Ifx ( Box  Ifx (b  :← a))
pattern b  :↾ a =  Dia  Ifx ( Box  Ifx (b  :← a))
pattern b :%↾ a = SDia SIfx (SBox SIfx (b :%← a))



-- * Operations on Types and Structures

data Focus (z :: StructI) :: * where
     Focus :: SStrength k -> SContext x -> SStructI y -> Plug x y :~: z -> Focus z

deriving instance (Show (Focus z))

data Trail (z :: StructI) :: * where
     Trail :: SStrength k -> SContext x -> Trace k x :~: z -> Trail z

deriving instance (Show (Trail z))

sPlug :: SContext x -> SStructI z -> SStructI (Plug x z)
sPlug SHOLE      z = z
sPlug (SDelW1 x) z = SDIA (SDelim SWeak) (sPlug x z)
sPlug (x :%<∙ y) z = SPROD SSolid (sPlug x z) y
sPlug (x :%∙> y) z = SPROD SSolid x (sPlug y z)

sTrace :: SStrength k -> SContext x -> SStructI (Trace k x)
sTrace k       SHOLE      = SUNIT (SQuan k)
sTrace SStrong (SDelW1 x) = SPROD SSolid SI' (SDIA (SDelim SWeak) (sTrace SStrong x))
sTrace k       (x :%∙> y) = SPROD SSolid (SPROD SSolid SB x) (sTrace k y)
sTrace k       (x :%<∙ y) = SPROD SSolid (SPROD SSolid SC (sTrace k x)) y

sFocus :: SStructI x -> [Focus x]
sFocus x = Focus SWeak SHOLE x Refl : sFocus' x
  where
    sFocus' :: SStructI x -> [Focus x]
    sFocus' (x :%∙ y) = (inx <$> sFocus x) ++ (iny <$> sFocus y)
      where
        inx (Focus k x z Refl) = Focus k (x :%<∙ y) z Refl
        iny (Focus k y z Refl) = Focus k (x :%∙> y) z Refl
    sFocus' (SDIA (SDelim SWeak) (x :: SStructI x)) = (inx <$> sFocus x)
      where
        inx :: Focus x -> Focus (DIA (Delim Weak) x)
        inx (Focus k x z Refl) = Focus SStrong (SDelW1 x) z Refl
    sFocus' x = []

sFollow :: SStructI x -> Maybe (Trail x)
sFollow  (SUNIT (SQuan k))      = Just (Trail k SHOLE Refl)
sFollow ((SC :%∙ x) :%∙ y)      = case sFollow x of
  Just (Trail k x Refl)        -> Just (Trail k (x :%<∙ y) Refl)
  _                            -> Nothing
sFollow ((SB :%∙ x) :%∙ y)      = case sFollow y of
  Just (Trail k y Refl)        -> Just (Trail k (x :%∙> y) Refl)
  _                            -> Nothing
sFollow (SI' :%∙ (SDIA (SDelim SWeak) x)) = case sFollow x of
  Just (Trail k x Refl)        -> Just (Trail k (SDelW1 x) Refl)
  _                            -> Nothing
sFollow _                       = Nothing


testFocus :: Bool
testFocus = length (sFocus (SStI (SEl SNP) :%∙ (SStI ((SEl SNP) :%→ (SEl SS))))) == 3



-- * Positive and Negative Types

data Pos :: Type -> * where
  Pos_Dia    :: Pos (Dia k a)
  Pos_UnitL  :: Pos (UnitL k a)
  Pos_With   :: Pos (a1 :& a2)

data Neg :: Type -> * where
  Neg_El     :: Neg (El a)
  Neg_Box    :: Neg (Box k a)
  Neg_ImpR   :: Neg (ImpR k a b)
  Neg_ImpL   :: Neg (ImpL k b a)

pol :: SType a -> Either (Pos a) (Neg a)
pol (SEl a)       = Right Neg_El
pol (_ :%& _)     = Left  Pos_With
pol (SDia _ _)    = Left  Pos_Dia
pol (SBox _ _)    = Right Neg_Box
pol (SUnitL _ _)  = Left  Pos_UnitL
pol (SImpR _ _ _) = Right Neg_ImpR
pol (SImpL _ _ _) = Right Neg_ImpL



-- * Instances

instance Show (SAtom     s) where show = show . fromSing
instance Show (SStrength s) where show = show . fromSing
instance Show (SKind     s) where show = show . fromSing
instance Show (SType     s) where show = show . fromSing
instance Show (SStructI  s) where show = show . fromSing
instance Show (SContext  s) where show = show . fromSing

instance Eq (SAtom     s) where x == y = fromSing x == fromSing y
instance Eq (SStrength s) where x == y = fromSing x == fromSing y
instance Eq (SKind     s) where x == y = fromSing x == fromSing y
instance Eq (SType     s) where x == y = fromSing x == fromSing y
instance Eq (SStructI  s) where x == y = fromSing x == fromSing y
instance Eq (SContext  s) where x == y = fromSing x == fromSing y

instance Ord (SAtom     s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SStrength s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SKind     s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SType     s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SStructI  s) where compare x y = compare (fromSing x) (fromSing y)




-- * Proofs

data Syn :: Sequent -> * where
  AxR    :: Pos b -> Syn (StI b :⊢> b)
  AxL    :: Neg a -> Syn (a :<⊢ StO a)
  UnfR   :: Neg b -> Syn (x :⊢ StO b) -> Syn (x :⊢> b)
  UnfL   :: Pos a -> Syn (StI a :⊢ y) -> Syn (a :<⊢ y)
  FocR   :: Pos b -> Syn (x :⊢> b) -> Syn (x :⊢ StO b)
  FocL   :: Neg a -> Syn (a :<⊢ y) -> Syn (StI a :⊢ y)

  WithL1 :: Syn (a1 :<⊢ y) -> Syn (StI (a1 :& a2) :⊢ y)
  WithL2 :: Syn (a2 :<⊢ y) -> Syn (StI (a1 :& a2) :⊢ y)
  WithR  :: Syn (x :⊢ StO b1) -> Syn (x :⊢ StO b2) -> Syn (x :⊢> b1 :& b2)

  ImpRL  :: Syn (x :⊢> a) -> Syn (b :<⊢ y) -> Syn (ImpR k a b :<⊢ IMPR k x y)
  ImpRR  :: Syn (x :⊢ IMPR k (StI a) (StO b)) -> Syn (x :⊢ StO (ImpR k a b))
  ImpLL  :: Syn (x :⊢> a) -> Syn (b :<⊢ y) -> Syn (ImpL k b a :<⊢ IMPL k y x)
  ImpLR  :: Syn (x :⊢ IMPL k (StO b) (StI a)) -> Syn (x :⊢ StO (ImpL k b a))
  ResRP  :: Syn (y :⊢ IMPR k x z) -> Syn (PROD k x y :⊢ z)
  ResPR  :: Syn (PROD k x y :⊢ z) -> Syn (y :⊢ IMPR k x z)
  ResLP  :: Syn (x :⊢ IMPL k z y) -> Syn (PROD k x y :⊢ z)
  ResPL  :: Syn (PROD k x y :⊢ z) -> Syn (x :⊢ IMPL k z y)

  DiaL   :: Syn (DIA k (StI a) :⊢ y) -> Syn (StI (Dia k a) :⊢ y)
  DiaR   :: Syn (x :⊢> b) -> Syn (DIA k x :⊢> Dia k b)
  BoxL   :: Syn (a :<⊢ y) -> Syn (Box k a :<⊢ BOX k y)
  BoxR   :: Syn (x :⊢ BOX k (StO b)) -> Syn (x :⊢ StO (Box k b))
  ResBD  :: Syn (x :⊢ BOX k y) -> Syn (DIA k x :⊢ y)
  ResDB  :: Syn (DIA k x :⊢ y) -> Syn (x :⊢ BOX k y)

  IfxRR   :: Syn ((x :∙ y) :∙ IFX z :⊢ w) -> Syn (x :∙ (y :∙ IFX z) :⊢ w)
  IfxLR   :: Syn ((x :∙ y) :∙ IFX z :⊢ w) -> Syn ((x :∙ IFX z) :∙ y :⊢ w)
  IfxLL   :: Syn (IFX z :∙ (y :∙ x) :⊢ w) -> Syn ((IFX z :∙ y) :∙ x :⊢ w)
  IfxRL   :: Syn (IFX z :∙ (y :∙ x) :⊢ w) -> Syn (y :∙ (IFX z :∙ x) :⊢ w)

  ExtRR   :: Syn (x :∙ (y :∙ EXT z) :⊢ w) -> Syn ((x :∙ y) :∙ EXT z :⊢ w)
  ExtLR   :: Syn ((x :∙ EXT z) :∙ y :⊢ w) -> Syn ((x :∙ y) :∙ EXT z :⊢ w)
  ExtLL   :: Syn ((EXT z :∙ y) :∙ x :⊢ w) -> Syn (EXT z :∙ (y :∙ x) :⊢ w)
  ExtRL   :: Syn (y :∙ (EXT z :∙ x) :⊢ w) -> Syn (EXT z :∙ (y :∙ x) :⊢ w)

  UnitLL :: Syn (PROD k (UNIT k) (StI a) :⊢ y) -> Syn (StI (UnitL k a) :⊢ y)
  UnitLR :: Syn (x :⊢> b) -> Syn (PROD k (UNIT k) x :⊢> UnitL k b)
  UnitLI :: Syn (x :⊢ y) -> Syn (PROD k (UNIT k) x :⊢ y)

  DnB    :: Syn (x :∙ (PROD (Quan k) y z) :⊢ w) -> Syn (PROD (Quan k) ((B :∙ x) :∙ y) z :⊢ w)
  UpB    :: Syn (PROD (Quan k) ((B :∙ x) :∙ y) z :⊢ w) -> Syn (x :∙ (PROD (Quan k)  y z) :⊢ w)
  DnC    :: Syn ((PROD (Quan k) x y) :∙ z :⊢ w) -> Syn (PROD (Quan k) ((C :∙ x) :∙ z) y :⊢ w)
  UpC    :: Syn (PROD (Quan k) ((C :∙ x) :∙ z) y :⊢ w) -> Syn ((PROD (Quan k) x y) :∙ z :⊢ w)

  UpI'   :: Syn (PROD (Quan Strong) (I' :∙ DELW x) y :⊢ w) -> Syn (DELW (PROD (Quan Strong) x y) :⊢ w)
  DnI'   :: Syn (DELW (PROD (Quan Strong) x y) :⊢ w) -> Syn (PROD (Quan Strong) (I' :∙ DELW x) y :⊢ w)




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

up :: SStrength k -> SContext x
   -> Syn (Plug x y :⊢ z) -> Syn (PROD (Quan k) (Trace k x) y :⊢ z)
up k       SHOLE      f = UnitLI f
up k       (x :%<∙ y) f = DnC  (ResLP (unsafeCoerce (up k x (ResPL (unsafeCoerce f)))))
up k       (x :%∙> y) f = DnB  (ResRP (unsafeCoerce (up k y (ResPR (unsafeCoerce f)))))
up SStrong (SDelW1 x) f = DnI' (ResBD (unsafeCoerce (up SStrong x (ResDB (unsafeCoerce f)))))
up SWeak   (SDelW1 x) f = error "up: `strong' context used with `weak' quantifier"

down :: SStrength k -> SContext x
     -> Syn (PROD (Quan k) (Trace k x) (StI a) :⊢ z)
     -> Syn (Plug x (StI (UnitL (Quan k) a)) :⊢ z)
down k x f = unsafeCoerce (init x (unsafeCoerce (move x f)))
  where
    init :: SContext x
         -> Syn (Plug x (PROD (Quan k) (UNIT (Quan k)) (StI a)) :⊢ y)
         -> Syn (Plug x (StI (UnitL (Quan k) a)) :⊢ y)
    init SHOLE      f = UnitLL f
    init (x :%<∙ y) f = ResLP (unsafeCoerce (init x (ResPL (unsafeCoerce f))))
    init (x :%∙> y) f = ResRP (unsafeCoerce (init y (ResPR (unsafeCoerce f))))
    init (SDelW1 x) f = ResBD (unsafeCoerce (init x (ResDB (unsafeCoerce f))))
    move :: SContext x
         -> Syn (PROD (Quan k) (Trace k x) y :⊢ z)
         -> Syn (Plug x (PROD (Quan k) (UNIT (Quan k)) y) :⊢ z)
    move SHOLE      f = f
    move (x :%<∙ y) f = ResLP (unsafeCoerce (move x (ResPL (UpC (unsafeCoerce f)))))
    move (x :%∙> y) f = ResRP (unsafeCoerce (move y (ResPR (UpB (unsafeCoerce f)))))
    move (SDelW1 x) f = case k %~ SStrong of
      Proved Refl    -> ResBD (unsafeCoerce (move x (ResDB (UpI' (unsafeCoerce f)))))
      _              -> error "down: `strong' context used with `weak' quantifier"

qrL :: SStrength k -> SContext x
    -> Syn (Trace k x :⊢> b)
    -> Syn (c :<⊢ y)
    -> Syn (Plug x (StI (UnitL (Quan k) (ImpR (Quan k) b c))) :⊢ y)
qrL k x f g = unsafeCoerce (down k x (ResRP (FocL Neg_ImpR (ImpRL f g))))

qrR :: SStrength k -> SContext x
    -> Syn (Plug x (StI a) :⊢ StO b)
    -> Syn (Trace k x :⊢ StO (ImpL (Quan k) b a))
qrR k x f = ImpLR (ResPL (up k x f))




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
   | UResRP  USyn      | UResPR  USyn | UResLP  USyn      | UResPL USyn
   | UDiaL   USyn      | UDiaR   USyn | UBoxL   USyn      | UBoxR USyn
   | UResBD  USyn      | UResDB  USyn
   | UIfxRR  USyn      | UIfxLR  USyn | UIfxLL  USyn      | UIfxRL USyn
   | UExtRR  USyn      | UExtLR  USyn | UExtLL  USyn      | UExtRL USyn
   | UUnitLL USyn      | UUnitLR USyn | UUnitLI USyn
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
forget (ResRP  f)   = UResRP  (forget f)
forget (ResPR  f)   = UResPR  (forget f)
forget (ResLP  f)   = UResLP  (forget f)
forget (ResPL  f)   = UResPL  (forget f)
forget (DiaL   f)   = UDiaL   (forget f)
forget (DiaR   f)   = UDiaR   (forget f)
forget (BoxL   f)   = UBoxL   (forget f)
forget (BoxR   f)   = UBoxR   (forget f)
forget (ResBD  f)   = UResBD  (forget f)
forget (ResDB  f)   = UResDB  (forget f)
forget (IfxRR  f)   = UIfxRR  (forget f)
forget (IfxLR  f)   = UIfxLR  (forget f)
forget (IfxLL  f)   = UIfxLL  (forget f)
forget (IfxRL  f)   = UIfxRL  (forget f)
forget (ExtRR  f)   = UExtRR  (forget f)
forget (ExtLR  f)   = UExtLR  (forget f)
forget (ExtLL  f)   = UExtLL  (forget f)
forget (ExtRL  f)   = UExtRL  (forget f)
forget (UnitLL f)   = UUnitLL (forget f)
forget (UnitLR f)   = UUnitLR (forget f)
forget (UnitLI f)   = UUnitLI (forget f)
forget (DnB    f)   = UDnB    (forget f)
forget (UpB    f)   = UUpB    (forget f)
forget (DnC    f)   = UDnC    (forget f)
forget (UpC    f)   = UUpC    (forget f)

instance Ord (Syn s) where
  f `compare` g = forget f `compare` forget g


-- -}
-- -}
-- -}
-- -}
-- -}
