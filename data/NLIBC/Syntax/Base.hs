{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies,
    ViewPatterns, ScopedTypeVariables #-}
module NLIBC.Syntax.Base where


import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Singletons.TH (promote,promoteOnly,singletons)


singletons [d|

  data Atom :: * where
    S   :: Atom
    N   :: Atom
    NP  :: Atom
    PP  :: Atom
    INF :: Atom
    deriving (Eq,Show)

  data Kind :: * where
    Solid    :: Kind
    Hollow   :: Kind
    Reset    :: Kind
    Infixate :: Kind
    Extract  :: Kind
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

  |]


deriving instance Bounded Kind
deriving instance Enum Kind

kinds :: [Kind]
kinds = [minBound..maxBound]

deriving instance Ord Atom
deriving instance Ord Kind
deriving instance Ord Type
deriving instance Ord StructI


infixr 3 ∙, :∙, :%∙
infixr 5 :&, :%&
infixr 7 :→, :%→
infixl 7 :←, :%←

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

type     Ifx a =  Dia  Infixate ( Box  Infixate a)
pattern  Ifx a =  Dia  Infixate ( Box  Infixate a)
pattern SIfx a = SDia SInfixate (SBox SInfixate a)
type     IFX x =  DIA  Infixate x
pattern  IFX x =  DIA  Infixate x
pattern SIFX x = SDIA SInfixate x

type     Ext a =  Dia  Extract ( Box  Extract a)
pattern  Ext a =  Dia  Extract ( Box  Extract a)
pattern SExt a = SDia SExtract (SBox SExtract a)
type     EXT x =  DIA  Extract x
pattern  EXT x =  DIA  Extract x
pattern SEXT x = SDIA SExtract x

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


type family ToList (x :: StructI) :: [Type] where
  ToList (StI  a    ) = (a ': '[])
  ToList (DIA  k x  ) = ToList x
  ToList (PROD k x y) = ToList x :++ ToList y


toList :: SStructI x -> Maybe (SList (ToList x))
toList (SStI  a)     = Just (SCons a SNil)
toList (SDIA  k x)   = toList x
toList (SPROD k x y) = (%:++) <$> toList x <*> toList y
toList _             = Nothing
