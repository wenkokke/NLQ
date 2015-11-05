{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies #-}
module NLIBC.Syntax where


import           Control.Applicative (Alternative(empty,(<|>)))
import           Control.Monad (msum,MonadPlus(..))
import           Control.Monad.State.Strict (StateT,get,put,evalStateT)
import           Data.Maybe (maybeToList)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,promoteOnly,singletons)
import           Unsafe.Coerce (unsafeCoerce)


-- * Types, Structures and Sequents

singletons [d|

  data Atom :: * where
    S   :: Atom
    N   :: Atom
    NP  :: Atom
    PP  :: Atom
    INF :: Atom
    deriving (Eq,Show)

  data Kind :: * where
    Solid  :: Kind -- (←, ∙, →)
    Hollow :: Kind -- (⇦, ∘, ⇨)
    Reset  :: Kind -- (◇, □)
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

  |]

infix 1 ⊢, :⊢, :⊢>, :<⊢, :%⊢, :%⊢>, :%<⊢

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


deriving instance Ord Atom
deriving instance Ord Kind
deriving instance Ord Type
deriving instance Ord StructI
deriving instance Ord StructO
deriving instance Ord Sequent


-- * Contexts, Plugging and Traces

singletons [d|

  data Context :: * where
    HOLE  :: Context
    (:<∙) :: Context -> StructI -> Context
    (:∙>) :: StructI -> Context -> Context

  |]

infixr 3 :<∙, :∙>

promote [d|

  plug :: Context -> StructI -> StructI
  plug HOLE      z = z
  plug (x :<∙ y) z = PROD Solid (plug x z) y
  plug (x :∙> y) z = PROD Solid x (plug y z)

  trace :: Context -> StructI
  trace HOLE      = UNIT Hollow
  trace (x :∙> y) = PROD Solid (PROD Solid B x) (trace y)
  trace (x :<∙ y) = PROD Solid (PROD Solid C (trace x)) y

  |]

data Focus (z :: StructI) :: * where
     Focus :: SContext x -> SStructI y -> Plug x y :~: z -> Focus z

data Trail (z :: StructI) :: * where
     Trail :: SContext x -> Trace x :~: z -> Trail z

sPlug :: SContext x -> SStructI z -> SStructI (Plug x z)
sPlug SHOLE      z = z
sPlug (x :%<∙ y) z = SPROD SSolid (sPlug x z) y
sPlug (x :%∙> y) z = SPROD SSolid x (sPlug y z)

sTrace :: SContext x -> SStructI (Trace x)
sTrace SHOLE      = SUNIT SHollow
sTrace (x :%∙> y) = SPROD SSolid (SPROD SSolid SB x) (sTrace y)
sTrace (x :%<∙ y) = SPROD SSolid (SPROD SSolid SC (sTrace x)) y

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
sFollow (SUNIT SHollow) = Just (Trail SHOLE Refl)
sFollow (SPROD SSolid (SPROD SSolid SC x) y) = case sFollow x of
  Just (Trail x Refl) -> Just (Trail (x :%<∙ y) Refl)
  _                   -> Nothing
sFollow (SPROD SSolid (SPROD SSolid SB x) y) = case sFollow y of
  Just (Trail y Refl) -> Just (Trail (x :%∙> y) Refl)
  _                   -> Nothing
sFollow _                  = Nothing


-- * Type Abbreviations

infixr 3 ∙, :∙, :%∙

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

type    x  :∙ y =  PROD  Solid  x y
pattern x  :∙ y =  PROD  Solid  x y
pattern x :%∙ y = SPROD SSolid  x y
type    x  :→ y =  ImpR  Solid  x y
pattern x  :→ y =  ImpR  Solid  x y
pattern x :%→ y = SImpR SSolid  x y
type    y  :← x =  ImpL  Solid  y x
pattern y  :← x =  ImpL  Solid  y x
pattern y :%← x = SImpL SSolid  y x

type     QR x =  UnitR  Hollow x
pattern  QR x =  UnitR  Hollow x
pattern SQR x = SUnitR SHollow x

type     T =  UNIT  Hollow
pattern  T =  UNIT  Hollow
pattern ST = SUNIT SHollow

type    x  :∘ y =  PROD  Hollow x y
pattern x  :∘ y =  PROD  Hollow x y
pattern x :%∘ y = SPROD SHollow x y
type    x  :⇨ y =  ImpR  Hollow x y
pattern x  :⇨ y =  ImpR  Hollow x y
pattern x :%⇨ y = SImpR SHollow x y
type    y  :⇦ x =  ImpL  Hollow y x
pattern y  :⇦ x =  ImpL  Hollow y x
pattern y :%⇦ x = SImpL SHollow y x

type     Q a b c =  QR (c  :⇦ (a  :⇨ b))
pattern  Q a b c =  QR (c  :⇦ (a  :⇨ b))
pattern SQ a b c = SQR (c :%⇦ (a :%⇨ b))

type     Res a =  Dia  Reset a
pattern  Res a =  Dia  Reset a
pattern SRes a = SDia SReset a
type     RES x =  DIA  Reset x
pattern  RES x =  DIA  Reset x
pattern SRES x = SDIA SReset x


-- * Positive and Negative Types

data Pos :: Type -> * where
  Pos_N      :: Pos (El N)
  Pos_NP     :: Pos (El NP)
  Pos_PP     :: Pos (El PP)
  Pos_INF    :: Pos (El INF)
  Pos_Dia    :: Pos (Dia k a)
  Pos_UnitR  :: Pos (UnitR k a)

data Neg :: Type -> * where
  Neg_S      :: Neg (El S)
  Neg_Box    :: Neg (Box k a)
  Neg_With   :: Neg (a1 :& a2)
  Neg_ImpR   :: Neg (ImpR k a b)
  Neg_ImpL   :: Neg (ImpL k b a)

pol :: SType a -> Either (Pos a) (Neg a)
pol (SEl SS)      = Right Neg_S
pol (SEl SN)      = Left  Pos_N
pol (SEl SNP)     = Left  Pos_NP
pol (SEl SPP)     = Left  Pos_PP
pol (SEl SINF)    = Left  Pos_INF
pol (_ :%& _)     = Right Neg_With
pol (SDia _ _)    = Left  Pos_Dia
pol (SBox _ _)    = Right Neg_Box
pol (SUnitR _ _)  = Left  Pos_UnitR
pol (SImpR _ _ _) = Right Neg_ImpR
pol (SImpL _ _ _) = Right Neg_ImpL


-- * Proofs

data Prf :: Sequent -> * where
  AxR    :: Pos b -> Prf (StI b :⊢> b)
  AxL    :: Neg a -> Prf (a :<⊢ StO a)
  UnfR   :: Neg b -> Prf (x :⊢ StO b) -> Prf (x :⊢> b)
  UnfL   :: Pos a -> Prf (StI a :⊢ y) -> Prf (a :<⊢ y)
  FocR   :: Pos b -> Prf (x :⊢> b) -> Prf (x :⊢ StO b)
  FocL   :: Neg a -> Prf (a :<⊢ y) -> Prf (StI a :⊢ y)

  WithL1 :: Prf (a1 :<⊢ y) -> Prf (a1 :& a2 :<⊢ y)
  WithL2 :: Prf (a2 :<⊢ y) -> Prf (a1 :& a2 :<⊢ y)
  WithR  :: Prf (x :⊢> b1) -> Prf (x :⊢> b2) -> Prf (x :⊢> b1 :& b2)

  ImpRL  :: Prf (x :⊢> a) -> Prf (b :<⊢ y) -> Prf (ImpR k a b :<⊢ IMPR k x y)
  ImpRR  :: Prf (x :⊢ IMPR k (StI a) (StO b)) -> Prf (x :⊢ StO (ImpR k a b))
  ImpLL  :: Prf (x :⊢> a) -> Prf (b :<⊢ y) -> Prf (ImpL k b a :<⊢ IMPL k y x)
  ImpLR  :: Prf (x :⊢ IMPL k (StO b) (StI a)) -> Prf (x :⊢ StO (ImpL k b a))
  Res11  :: Prf (y :⊢ IMPR k x z) -> Prf (PROD k x y :⊢ z)
  Res12  :: Prf (PROD k x y :⊢ z) -> Prf (y :⊢ IMPR k x z)
  Res13  :: Prf (x :⊢ IMPL k z y) -> Prf (PROD k x y :⊢ z)
  Res14  :: Prf (PROD k x y :⊢ z) -> Prf (x :⊢ IMPL k z y)

  DiaL   :: Prf (DIA k (StI a) :⊢ y) -> Prf (StI (Dia k a) :⊢ y)
  DiaR   :: Prf (x :⊢> b) -> Prf (DIA k x :⊢> Dia k b)
  BoxL   :: Prf (a :<⊢ y) -> Prf (Box k a :<⊢ BOX k y)
  BoxR   :: Prf (x :⊢ BOX k (StO b)) -> Prf (x :⊢ StO (Box k b))
  Res21  :: Prf (x :⊢ BOX k y) -> Prf (DIA k x :⊢ y)
  Res22  :: Prf (DIA k x :⊢ y) -> Prf (x :⊢ BOX k y)

  UnitRL :: Prf (PROD k (StI a) (UNIT k) :⊢ y) -> Prf (StI (UnitR k a) :⊢ y)
  UnitRR :: Prf (x :⊢> b) -> Prf (PROD k x (UNIT k) :⊢> UnitR k b)
  UnitRI :: Prf (x :⊢ y) -> Prf (PROD k x (UNIT k) :⊢ y)

  DnB    :: Prf (x :∙ (y :∘ z) :⊢ w) -> Prf (y :∘ ((B :∙ x) :∙ z) :⊢ w)
  UpB    :: Prf (y :∘ ((B :∙ x) :∙ z) :⊢ w) -> Prf (x :∙ (y :∘ z) :⊢ w)
  DnC    :: Prf ((x :∘ y) :∙ z :⊢ w) -> Prf (x :∘ ((C :∙ y) :∙ z) :⊢ w)
  UpC    :: Prf (x :∘ ((C :∙ y) :∙ z) :⊢ w) -> Prf ((x :∘ y) :∙ z :⊢ w)


instance Show (SSequent s) where
  show ss = show (fromSing ss)

deriving instance Eq   (Pos s)
deriving instance Eq   (Neg s)
deriving instance Eq   (Prf s)
deriving instance Show (Pos s)
deriving instance Show (Neg s)
deriving instance Show (Prf s)


qrL :: SContext x
    -> Prf (Trace x :⊢> b)
    -> Prf (c :<⊢ y)
    -> Prf (Plug x (StI (QR (c :⇦ b))) :⊢ y)
qrL x f g = unsafeCoerce . init x
          $ unsafeCoerce . move x
          $ Res13 (FocL Neg_ImpL (ImpLL f g))
  where
    init :: SContext x
         -> Prf (Plug x (StI a :∘ T) :⊢ y)
         -> Prf (Plug x (StI (QR a)) :⊢ y)
    init SHOLE      f = UnitRL f
    init (x :%<∙ y) f = Res13 (unsafeCoerce (init x (Res14 (unsafeCoerce f))))
    init (x :%∙> y) f = Res11 (unsafeCoerce (init y (Res12 (unsafeCoerce f))))

    move :: SContext x
         -> Prf (y :∘ Trace x :⊢ z)
         -> Prf (Plug x (y :∘ T) :⊢ z)
    move SHOLE      f = f
    move (x :%<∙ y) f = Res13 (unsafeCoerce (move x (Res14 (UpC (unsafeCoerce f)))))
    move (x :%∙> y) f = Res11 (unsafeCoerce (move y (Res12 (UpB (unsafeCoerce f)))))


qrR :: SContext x
    -> Prf (Plug x (StI a) :⊢ StO b)
    -> Prf (Trace x :⊢ StO (a :⇨ b))
qrR x f = ImpRR (Res12 (move x f))
  where
    move :: SContext x
         -> Prf (Plug x y :⊢ z)
         -> Prf (y :∘ Trace x :⊢ z)
    move SHOLE      f = UnitRI f
    move (x :%<∙ y) f = DnC (Res13 (unsafeCoerce (move x (Res14 (unsafeCoerce f)))))
    move (x :%∙> y) f = DnB (Res11 (unsafeCoerce (move y (Res12 (unsafeCoerce f)))))


-- * Proof search

type Search m a = (MonadPlus m) => StateT (Set Sequent) m a

find :: SSequent s -> Maybe (Prf s)
find ss = evalStateT (search ss) Set.empty

findAll :: SSequent s -> [Prf s]
findAll ss = evalStateT (search ss) Set.empty

search :: SSequent s -> Search m (Prf s)
search ss = do
  visited <- get
  put (Set.insert (fromSing ss) visited)
  msum (fmap ($ ss) nl)
  where
    nl = concat
          [ [axR,axL,unfR,unfL,focR,focL]
          , [withL1,withL2,withR]
          , [impRL,impRR,impLL,impLR,res11,res12,res13,res14]
          , [diaL,diaR,boxL,boxR,res21,res22]
          , [unitL,unitR,unitI]
          , [up,dn]
          ]

    loop :: SSequent s -> Search m (Prf s)
    loop ss = do
      let s = fromSing ss
      visited <- get
      if (Set.member s visited)
        then empty
        else put (Set.insert s visited) >> search ss

    prog :: SSequent s -> Search m (Prf s)
    prog ss = do put (Set.empty); search ss


    axR, axL, unfR, unfL, focR, focL :: SSequent s -> Search m (Prf s)
    axR  (SStI a :%⊢> b) = case (b %~ a, pol b) of { (Proved Refl, Left  p) -> pure (AxR p); _ -> empty }
    axR  _               = empty
    axL  (a :%<⊢ SStO b) = case (a %~ b, pol a) of { (Proved Refl, Right p) -> pure (AxL p); _ -> empty }
    axL  _               = empty
    unfR (x :%⊢> b)      = case pol b of { Right p -> UnfR p <$> loop (x :%⊢ SStO b); _ -> empty }
    unfR  _              = empty
    unfL (a :%<⊢ y)      = case pol a of { Left  p -> UnfL p <$> loop (SStI a :%⊢ y); _ -> empty }
    unfL  _              = empty
    focR (x :%⊢ SStO b)  = case pol b of { Left  p -> FocR p <$> loop (x :%⊢> b); _ -> empty }
    focR  _              = empty
    focL (SStI a :%⊢ y)  = case pol a of { Right p -> FocL p <$> loop (a :%<⊢ y); _ -> empty }
    focL  _              = empty

    withL1,withL2,withR :: SSequent s -> Search m (Prf s)
    withL1 (a1 :%& a2 :%<⊢ y) = WithL1 <$> prog (a1 :%<⊢ y)
    withL1 _                  = empty
    withL2 (a1 :%& a2 :%<⊢ y) = WithL2 <$> prog (a2 :%<⊢ y)
    withL2 _                  = empty
    withR  (x :%⊢> b1 :%& b2) = WithR  <$> prog (x :%⊢> b1) <*> prog (x :%⊢> b2)
    withR  _                  = empty


    impRL,impRR,impLL,impLR,res11,res12,res13,res14 :: SSequent s -> Search m (Prf s)
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


    diaL, diaR, boxL, boxR, res21, res22 :: SSequent s -> Search m (Prf s)
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


    unitL,unitR,unitI :: SSequent s -> Search m (Prf s)
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


    dnB, dnC, upB, upC :: SSequent s -> Search m (Prf s)
    upB (x :%∙ (y :%∘ z) :%⊢ w)          = UpB <$> loop (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w)
    upB _                                = empty
    dnB (y :%∘ ((SB :%∙ x) :%∙ z) :%⊢ w) = DnB <$> loop (x :%∙ (y :%∘ z) :%⊢ w)
    dnB _                                = empty
    upC ((x :%∘ y) :%∙ z :%⊢ w)          = UpC <$> loop (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w)
    upC _                                = empty
    dnC (x :%∘ ((SC :%∙ y) :%∙ z) :%⊢ w) = DnC <$> loop ((x :%∘ y) :%∙ z :%⊢ w)
    dnC _                                = empty


    up,dn :: SSequent s -> Search m (Prf s)
    up (x :%⊢ y)              = msum (app <$> sFocus x)
      where
        app (Focus x (SStI (SQR (c :%⇦ b))) Refl)
                              = qrL x <$> prog (sTrace x :%⊢> b) <*> prog (c :%<⊢ y)
        app _                 = empty
    up _                      = empty
    dn (x :%⊢ SStO (a :%⇨ b)) = msum (maybeToList (app <$> sFollow x))
      where
        app (Trail x Refl)    = qrR x <$> prog (sPlug x (SStI a) :%⊢ SStO b)
    dn _                      = empty
