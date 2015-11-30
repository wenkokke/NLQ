{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies,
    ViewPatterns, ScopedTypeVariables #-}
module NLIBC.Syntax.Forward where


import           NLIBC.Syntax.Base
import           Control.Applicative (Alternative(empty,(<|>)))
import           Control.Monad (msum,MonadPlus(..))
import           Control.Monad.State.Strict (StateT,get,put,evalStateT)
import qualified Data.List.Ordered as OL
import qualified Data.List as L
import           Data.Maybe (isJust,fromJust,catMaybes,mapMaybe)
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Singletons.Decide
import           Data.Singletons.Prelude
import           Data.Singletons.TH (promote,promoteOnly,singletons)
import           Debug.Trace (traceShow)
import           Unsafe.Coerce (unsafeCoerce)


singletons [d|

  data Context :: * where
    HOLE  :: Context
    DIA1  :: Kind -> Context -> Context
    PROD1 :: Kind -> Context -> StructI -> Context
    PROD2 :: Kind -> StructI -> Context -> Context
    deriving (Eq,Show)

  data Sequent :: * where
    (:⊢) :: StructI -> Type -> Sequent
    deriving (Eq,Show)

  |]

infix  1 :⊢, :%⊢

infixr 3 :%<∙, :%∙>

pattern x :%<∙ y = SPROD1 SSolid x y
pattern x :%∙> y = SPROD2 SSolid x y

promote [d|

  plug :: Context -> StructI -> StructI
  plug  HOLE         z = z
  plug (DIA1  k x)   z = DIA  k (plug x z)
  plug (PROD1 k x y) z = PROD k (plug x z) y
  plug (PROD2 k x y) z = PROD k x (plug y z)

  |]

promote [d|

  prim :: Type -> [Type]
  prim a = a : primPos a

  primPos :: Type -> [Type]
  primPos (El    a)     = []
  primPos (Dia   k a)   = a : primPos a
  primPos (Box   k a)   =     primNeg a
  primPos (UnitR k a)   = a : primPos a
  primPos (ImpR  k a b) =     primNeg a -- todo: do something with b
  primPos (ImpL  k b a) =     primNeg a -- todo: do something with b

  primNeg :: Type -> [Type]
  primNeg (El    a)     = []
  primNeg (Dia   k a)   =     primNeg a
  primNeg (Box   k a)   = a : primPos a
  primNeg (UnitR k a)   =     primNeg a
  primNeg (ImpR  k a b) = a : primPos a -- todo: do something with b
  primNeg (ImpL  k b a) = a : primPos a -- todo: do something with b

  |]

data Focus (z :: StructI) :: * where
     Focus :: SContext x -> SStructI y -> Plug x y :~: z -> Focus z

sPlug :: SContext x -> SStructI z -> SStructI (Plug x z)
sPlug  SHOLE         z = z
sPlug (SDIA1   k x)  z = SDIA  k (sPlug x z)
sPlug (SPROD1 k x y) z = SPROD k (sPlug x z) y
sPlug (SPROD2 k x y) z = SPROD k x (sPlug y z)

sFocus :: SStructI x -> [Focus x]
sFocus x = Focus SHOLE x Refl : sFocus' x
  where
    sFocus' :: SStructI x -> [Focus x]
    sFocus' (SDIA  k x)   = (inx <$> sFocus x)
      where
        inx (Focus x z Refl) = Focus (SDIA1 k x) z Refl
    sFocus' (SPROD k x y) = (inx <$> sFocus x) ++ (iny <$> sFocus y)
      where
        inx (Focus x z Refl) = Focus (SPROD1 k x y) z Refl
        iny (Focus y z Refl) = Focus (SPROD2 k x y) z Refl
    sFocus' x         = []

sPrim :: SType a -> SList (Prim a)
sPrim a = SCons a (sPrimPos a)
  where
    sPrimPos :: SType a -> SList (PrimPos a)
    sPrimPos (SEl    a)     = SNil
    sPrimPos (SDia   k a)   = SCons a (sPrimPos a)
    sPrimPos (SBox   k a)   =          sPrimNeg a
    sPrimPos (SUnitR k a)   = SCons a (sPrimPos a)
    sPrimPos (SImpR  k a b) =          sPrimNeg a
    sPrimPos (SImpL  k b a) =          sPrimNeg a
    sPrimNeg :: SType a -> SList (PrimNeg a)
    sPrimNeg (SEl    a)     = SNil
    sPrimNeg (SDia   k a)   =          sPrimNeg a
    sPrimNeg (SBox   k a)   = SCons a (sPrimPos a)
    sPrimNeg (SUnitR k a)   =          sPrimNeg a
    sPrimNeg (SImpR  k a b) = SCons a (sPrimPos a)
    sPrimNeg (SImpL  k b a) = SCons a (sPrimPos a)


data Syn :: Sequent -> * where

  Ax     :: Syn (StI a :⊢ a)

  ImpRI  :: Syn (PROD k (StI a) x :⊢ b)
         -> Syn (x :⊢ ImpR k a b)
  ImpRE  :: Syn (x :⊢ a)
         -> Syn (y :⊢ ImpR k a b)
         -> Syn (PROD k x y :⊢ b)

  ImpLI  :: Syn (PROD k x (StI a) :⊢ b)
         -> Syn (x :⊢ ImpL k b a)
  ImpLE  :: Syn (x :⊢ ImpL k b a)
         -> Syn (y :⊢ a)
         -> Syn (PROD k x y :⊢ b)

  WithI  :: Syn (x :⊢ a)
         -> Syn (x :⊢ b)
         -> Syn (x :⊢ a :& b)
  WithE1 :: Syn (x :⊢ a :& b)
         -> Syn (x :⊢ a)
  WithE2 :: Syn (x :⊢ a :& b)
         -> Syn (x :⊢ b)

  BoxI   :: Syn (DIA k x :⊢ a)
         -> Syn (x :⊢ Box k a)
  BoxE   :: Syn (x :⊢ Box k a)
         -> Syn (DIA k x :⊢ a)
  DiaI   :: Syn (x :⊢ a)
         -> Syn (DIA k x :⊢ Dia k a)
  DiaE   :: SContext w
         -> Syn (x :⊢ Dia k a)
         -> Syn (Plug w (DIA k (StI a)) :⊢ b)
         -> Syn (Plug w x :⊢ b)

  UnitRI :: Syn (x :⊢ b)
         -> Syn (PROD k x (UNIT k) :⊢ b)
  UnitRE :: SContext y
         -> Syn (x :⊢ UnitR k a)
         -> Syn (Plug y (PROD k (StI a) (UNIT k)) :⊢ b)
         -> Syn (Plug y x :⊢ b)

  IfxRR  :: SContext w
         -> Syn (Plug w ((x :∙ y) :∙ IFX z) :⊢ a)
         -> Syn (Plug w (x :∙ (y :∙ IFX z)) :⊢ a)
  IfxLR  :: SContext w
         -> Syn (Plug w ((x :∙ y) :∙ IFX z) :⊢ a)
         -> Syn (Plug w ((x :∙ IFX z) :∙ y) :⊢ a)
  IfxLL  :: SContext w
         -> Syn (Plug w (IFX z :∙ (y :∙ x)) :⊢ a)
         -> Syn (Plug w ((IFX z :∙ y) :∙ x) :⊢ a)
  IfxRL  :: SContext w
         -> Syn (Plug w (IFX z :∙ (y :∙ x)) :⊢ a)
         -> Syn (Plug w (y :∙ (IFX z :∙ x)) :⊢ a)

  ExtRR  :: SContext w
         -> Syn (Plug w (x :∙ (y :∙ EXT z)) :⊢ a)
         -> Syn (Plug w ((x :∙ y) :∙ EXT z) :⊢ a)
  ExtLR  :: SContext w
         -> Syn (Plug w ((x :∙ EXT z) :∙ y) :⊢ a)
         -> Syn (Plug w ((x :∙ y) :∙ EXT z) :⊢ a)
  ExtLL  :: SContext w
         -> Syn (Plug w ((EXT z :∙ y) :∙ x) :⊢ a)
         -> Syn (Plug w (EXT z :∙ (y :∙ x)) :⊢ a)
  ExtRL  :: SContext w
         -> Syn (Plug w (y :∙ (EXT z :∙ x)) :⊢ a)
         -> Syn (Plug w (EXT z :∙ (y :∙ x)) :⊢ a)

  DnB    :: SContext w
         -> Syn (Plug w (x :∙ (y :∘ z)) :⊢ a)
         -> Syn (Plug w (y :∘ ((B :∙ x) :∙ z)) :⊢ a)
  UpB    :: SContext w
         -> Syn (Plug w (y :∘ ((B :∙ x) :∙ z)) :⊢ a)
         -> Syn (Plug w (x :∙ (y :∘ z)) :⊢ a)
  DnC    :: SContext w
         -> Syn (Plug w ((x :∘ y) :∙ z) :⊢ a)
         -> Syn (Plug w (x :∘ ((C :∙ y) :∙ z)) :⊢ a)
  UpC    :: SContext w
         -> Syn (Plug w (x :∘ ((C :∙ y) :∙ z)) :⊢ a)
         -> Syn (Plug w ((x :∘ y) :∙ z) :⊢ a)


-- * Instances

deriving instance Show (Syn s)
deriving instance Ord Context
deriving instance Ord Sequent

instance Show (SContext s) where show = show . fromSing
instance Show (SSequent s) where show = show . fromSing

instance Eq (SContext s) where x == y = fromSing x == fromSing y
instance Eq (SSequent s) where x == y = fromSing x == fromSing y
instance Eq (Syn s)      where (==) = eq

instance Ord (SContext s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (SSequent s) where compare x y = compare (fromSing x) (fromSing y)
instance Ord (Syn s)      where compare = ord


-- * Dynamically-typed proofs

data Typed where
  Typed :: SSequent s -> Syn s -> Typed

instance Show Typed where
  show (Typed _ f) = show f

instance Eq Typed where
  Typed t1 x1 == Typed t2 x2 =
    case t1 %~ t2 of { Proved Refl -> eq x1 x2 ; _ -> False }

instance Ord Typed where
  Typed t1 x1 `compare` Typed t2 x2 =
    case fromSing t1 `compare` fromSing t2 of { EQ -> ord x1 x2 ; o -> o }


-- * Proofs indexed by a list of words

data TypedBy (xs :: [Type]) (b :: Type) where
     TypedBy :: SStructI x -> ToList x :~: xs -> Syn (x :⊢ b) -> TypedBy xs y

instance Show (TypedBy xs b) where
  show (TypedBy _ _ f) = show f

before :: SList (xs :: [Type]) -> [Typed]
before = L.sort . wrapWithPrim
  where
    wrap :: SList (xs :: [Type]) -> [Typed]
    wrap   SNil        = []
    wrap  (SCons x xs) = Typed (SStI x :%⊢ x) Ax : wrap xs
    wrapWithPrim :: SList (xs :: [Type]) -> [Typed]
    wrapWithPrim  SNil        = []
    wrapWithPrim (SCons x xs) = wrap (sPrim x) ++ wrapWithPrim xs

after :: SList xs -> SType b -> [Typed] -> Maybe (TypedBy xs b)
after xs1 b1 [Typed (x :%⊢ b2) f] =
  case b1 %~ b2 of
  Disproved _ -> Nothing ; Proved Refl ->
    case toList x of
    Nothing  -> Nothing ; Just xs2 ->
      case xs2 %~ xs1 of
      Disproved _ -> Nothing ; Proved Refl -> Just (TypedBy x Refl f)
after _ _ _ = Nothing


topDown :: Int -> SList (xs :: [Type]) -> SType b -> [TypedBy xs b]
topDown n lst b = mapMaybe (after lst b) (go n [] [before lst])
  where
    go :: Int -> [[Typed]] -> [[Typed]] -> [[Typed]]
    go 0 old new = old ++ new
    go n old new = go (n-1) (old ++ new) (concatMap next new)

    next :: [Typed] -> [[Typed]]
    next bag = concat $
      [ ins (f x)   (del [x]   bag) | f <- fun1, x <- bag ] ++
      [ ins (f x y) (del [x,y] bag) | f <- fun2, x <- bag, y <- bag ]
      where
        ins :: [Typed] -> [Typed] -> [[Typed]]
        ins ys xs = do y <- ys; return (OL.insertBag y xs)
        del :: [Typed] -> [Typed] -> [Typed]
        del ys xs = OL.minus xs (L.sort ys)
        fun1 = [impRI,impLI,unitRI,dnB,upB,dnC,upC]
        fun2 = [impRE,impLE,unitRE]


impRE,impLE :: Typed -> Typed -> [Typed]
impRE (Typed (x :%⊢ a1) f) (Typed (y :%⊢ SImpR k a2 b) g)
  = case a1 %~ a2 of
  Proved Refl -> return (Typed (SPROD k x y :%⊢ b) (ImpRE f g))
  _           -> empty
impRE _ _ = empty
impLE (Typed (x :%⊢ SImpL k b a1) f) (Typed (y :%⊢ a2) g)
  = case a1 %~ a2 of
  Proved Refl -> return (Typed (SPROD k x y :%⊢ b) (ImpLE f g))
  _           -> empty
impLE _ _ = empty

impRI,impLI :: Typed -> [Typed]
impRI (Typed (SPROD k (SStI a) x :%⊢ b) f)
  = return (Typed (x :%⊢ SImpR k a b) (ImpRI f))
impRI _ = empty
impLI (Typed (SPROD k x (SStI a) :%⊢ b) f)
  = return (Typed (x :%⊢ SImpL k b a) (ImpLI f))
impLI _ = empty

unitRE :: Typed -> Typed -> [Typed]
unitRE (Typed (x :%⊢ SUnitR k1 a1) f) (Typed (w :%⊢ b) g) = concatMap go (sFocus w)
  where
    go (Focus w (SPROD k2 (SStI a2) (SUNIT k3)) Refl) =
      case k1 %~ k2 of
      Disproved _ -> empty ; Proved Refl ->
        case k1 %~ k3 of
        Disproved _ -> empty ; Proved Refl ->
          case a1 %~ a2 of
          Disproved _ -> empty ; Proved Refl ->
            return (Typed (sPlug w x :%⊢ b) (UnitRE w f g))
    go _ = empty
unitRE _ _ = empty

unitRI :: Typed -> [Typed]
unitRI (Typed (x :%⊢ b) f)
  = return (Typed (x :%∘ ST :%⊢ b) (UnitRI f))

dnB,upB,dnC,upC :: Typed -> [Typed]
dnB (Typed _ (UpB _ _)) = empty
dnB (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w (x :%∙ (y :%∘ z)) Refl) =
      return (Typed (sPlug w (y :%∘ ((SB :%∙ x) :%∙ z)) :%⊢ b)
                    (unsafeCoerce (DnB w (unsafeCoerce f))))
    go _ = empty
upB (Typed _ (DnB _ _)) = empty
upB (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w (y :%∘ ((SB :%∙ x) :%∙ z)) Refl) =
      return (Typed (sPlug w (x :%∙ (y :%∘ z)) :%⊢ b)
                    (unsafeCoerce (UpB w (unsafeCoerce f))))
    go _ = empty
dnC (Typed _ (UpC _ _)) = empty
dnC (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w ((x :%∘ y) :%∙ z) Refl) =
      return (Typed (sPlug w (x :%∘ ((SC :%∙ y) :%∙ z)) :%⊢ b)
                    (unsafeCoerce (DnC w (unsafeCoerce f))))
    go _ = empty
upC (Typed _ (DnC _ _)) = empty
upC (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w (x :%∘ ((SC :%∙ y) :%∙ z)) Refl) =
      return (Typed (sPlug w ((x :%∘ y) :%∙ z) :%⊢ b)
                    (unsafeCoerce (UpC w (unsafeCoerce f))))
    go _ = empty


type NP = El 'NP   ; sNP  = SEl SNP
type S  = El 'S    ; sS   = SEl SS
type N  = El 'N    ; sN   = SEl SN
type IV = NP :→ S  ; sIV  = sNP :%→ sS
type TV = IV :← NP ; sTV  = sIV :%← sNP
infixr 4 %: ; (%:) = SCons

test1 :: [TypedBy [NP,IV] S]
test1 = topDown 1 (sNP %: sIV %: SNil) sS
test2 :: [TypedBy [NP,TV,NP] S]
test2 = topDown 2 (sNP %: sTV %: sNP %: SNil) sS
test3 :: [TypedBy [Q NP S S,IV] S]
test3 = topDown 7 (SQ sNP sS sS %: sIV %: SNil) sS
test4 :: [TypedBy [Q NP S S,TV,NP] S]
test4 = topDown 8 (SQ sNP sS sS %: sTV %: sNP %: SNil) sS
test5 :: [TypedBy [NP,TV,Q NP S S] S]
test5 = topDown 10 (sNP %: sTV %: SQ sNP sS sS %: SNil) sS

{-
diaE :: Typed -> Typed -> [Typed]
diaE (Typed (x :%⊢ SDia k1 a1) f) (Typed (w :%⊢ b) g) = concatMap go (sFocus w)
  where
    go (Focus w (SDIA k2 (SStI a2)) Refl) =
      case k1 %~ k2 of
      Disproved _ -> empty ; Proved Refl ->
        case a1 %~ a2 of
        Disproved _ -> empty ; Proved Refl ->
          return (Typed (sPlug w x :%⊢ b) (DiaE w f g))
    go _ = empty
diaE _ _ = empty

withE :: Typed -> [Typed]
withE (Typed _ (WithI _ _))     = empty
withE (Typed (x :%⊢ a :%& b) f) = [Typed (x :%⊢ a) (WithE1 f),Typed (x :%⊢ b) (WithE2 f)]
withE _                         = empty

boxI,boxE :: Typed -> [Typed]
boxI (Typed (SDIA k x :%⊢ a) f) = return (Typed (x :%⊢ SBox k a) (BoxI f))
boxI _                          = empty
boxE (Typed _ (BoxI _))         = empty
boxE (Typed (x :%⊢ SBox k a) f) = return (Typed (SDIA k x :%⊢ a) (BoxE f))
boxE _                          = empty

unitRI :: Typed -> [Typed]
unitRI (Typed (x :%⊢ b) f) = return (Typed (x :%∘ ST :%⊢ b) (UnitRI f))

dnB,upB,dnC,upC :: Typed -> [Typed]
dnB (Typed _ (UpB _ _)) = empty
dnB (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w (x :%∙ (y :%∘ z)) Refl) =
      return $ Typed (sPlug w (y :%∘ ((SB :%∙ x) :%∙ z)) :%⊢ b)
                     (unsafeCoerce (DnB w (unsafeCoerce f)))
    go _ = empty
upB (Typed _ (DnB _ _)) = empty
upB (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w (y :%∘ ((SB :%∙ x) :%∙ z)) Refl) =
      return $ Typed (sPlug w (x :%∙ (y :%∘ z)) :%⊢ b)
                     (unsafeCoerce (UpB w (unsafeCoerce f)))
    go _ = empty
dnC (Typed _ (UpC _ _)) = empty
dnC (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w ((x :%∘ y) :%∙ z) Refl) =
      return $ Typed (sPlug w (x :%∘ ((SC :%∙ y) :%∙ z)) :%⊢ b)
                     (unsafeCoerce (DnC w (unsafeCoerce f)))
    go _ = empty
upC (Typed _ (DnC _ _)) = empty
upC (Typed (w :%⊢ b) f) = concatMap go (sFocus w)
  where
    go (Focus w (x :%∘ ((SC :%∙ y) :%∙ z)) Refl) =
      return $ Typed (sPlug w ((x :%∘ y) :%∙ z) :%⊢ b)
                     (unsafeCoerce (UpC w (unsafeCoerce f)))
    go _ = empty

{-
-- * Proof search

  IfxRR  :: SContext w
         -> (Plug w ((x :∙ y) :∙ IFX z) :⊢ a)
         -> (Plug w (x :∙ (y :∙ IFX z)) :⊢ a)
  IfxLR  :: SContext w
         -> (Plug w ((x :∙ y) :∙ IFX z) :⊢ a)
         -> (Plug w ((x :∙ IFX z) :∙ y) :⊢ a)
  IfxLL  :: SContext w
         -> (Plug w (IFX z :∙ (y :∙ x)) :⊢ a)
         -> (Plug w ((IFX z :∙ y) :∙ x) :⊢ a)
  IfxRL  :: SContext w
         -> (Plug w (IFX z :∙ (y :∙ x)) :⊢ a)
         -> (Plug w (y :∙ (IFX z :∙ x)) :⊢ a)
  ExtRR  :: SContext w
         -> (Plug w (x :∙ (y :∙ EXT z)) :⊢ a)
         -> (Plug w ((x :∙ y) :∙ EXT z) :⊢ a)
  ExtLR  :: SContext w
         -> (Plug w ((x :∙ EXT z) :∙ y) :⊢ a)
         -> (Plug w ((x :∙ y) :∙ EXT z) :⊢ a)
  ExtLL  :: SContext w
         -> (Plug w ((EXT z :∙ y) :∙ x) :⊢ a)
         -> (Plug w (EXT z :∙ (y :∙ x)) :⊢ a)
  ExtRL  :: SContext w
         -> (Plug w (y :∙ (EXT z :∙ x)) :⊢ a)
         -> (Plug w (EXT z :∙ (y :∙ x)) :⊢ a)

-- -}
-- -}
-- -}
-- -}
-- -}

eq :: Syn s1 -> Syn s2 -> Bool
eq (Ax          ) (Ax          ) = True
eq (ImpRI  x    ) (ImpRI  u    ) = x `eq` u
eq (ImpRE  x y  ) (ImpRE  u v  ) = x `eq` u
eq (ImpLI  x    ) (ImpLI  u    ) = x `eq` u
eq (ImpLE  x y  ) (ImpLE  u v  ) = x `eq` u
eq (WithI  x y  ) (WithI  u v  ) = x `eq` u
eq (WithE1 x    ) (WithE1 u    ) = x `eq` u
eq (WithE2 x    ) (WithE2 u    ) = x `eq` u
eq (BoxI   x    ) (BoxI   u    ) = x `eq` u
eq (BoxE   x    ) (BoxE   u    ) = x `eq` u
eq (DiaI   x    ) (DiaI   u    ) = x `eq` u
eq (DiaE   x y z) (DiaE   u v w) =
   case x %~ u of { Proved Refl -> y `eq` v && z `eq` w ; _ -> False }
eq (UnitRI x    ) (UnitRI u    ) = x `eq` u
eq (UnitRE x y z) (UnitRE u v w) =
   case x %~ u of { Proved Refl -> y `eq` v && z `eq` w ; _ -> False }
eq (IfxRR  x y  ) (IfxRR  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (IfxLR  x y  ) (IfxLR  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (IfxLL  x y  ) (IfxLL  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (IfxRL  x y  ) (IfxRL  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (ExtRR  x y  ) (ExtRR  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (ExtLR  x y  ) (ExtLR  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (ExtLL  x y  ) (ExtLL  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (ExtRL  x y  ) (ExtRL  u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (DnB    x y  ) (DnB    u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (UpB    x y  ) (UpB    u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (DnC    x y  ) (DnC    u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (UpC    x y  ) (UpC    u v  ) =
   case x %~ u of { Proved Refl -> y `eq` v ; _ -> False }
eq (_           ) (_           ) = False


ord :: Syn s1 -> Syn s2 -> Ordering
ord (Ax          ) uvw = case uvw of
    (Ax          ) -> EQ
    (ImpRI  u    ) -> GT
    (ImpRE  u v  ) -> GT
    (ImpLI  u    ) -> GT
    (ImpLE  u v  ) -> GT
    (WithI  u v  ) -> GT
    (WithE1 u    ) -> GT
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ImpRI  x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> ord x u
    (ImpRE  u v  ) -> GT
    (ImpLI  u    ) -> GT
    (ImpLE  u v  ) -> GT
    (WithI  u v  ) -> GT
    (WithE1 u    ) -> GT
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ImpRE  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> case ord x u of { EQ -> ord y v ; o -> o }
    (ImpLI  u    ) -> GT
    (ImpLE  u v  ) -> GT
    (WithI  u v  ) -> GT
    (WithE1 u    ) -> GT
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ImpLI  x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> ord x u
    (ImpLE  u v  ) -> GT
    (WithI  u v  ) -> GT
    (WithE1 u    ) -> GT
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ImpLE  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> case ord x u of { EQ -> ord y v ; o -> o }
    (WithI  u v  ) -> GT
    (WithE1 u    ) -> GT
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (WithI  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> case ord x u of { EQ -> ord y v ; o -> o }
    (WithE1 u    ) -> GT
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (WithE1 x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> ord x u
    (WithE2 u    ) -> GT
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (WithE2 x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> ord x u
    (BoxI   u    ) -> GT
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (BoxI   x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> ord x u
    (BoxE   u    ) -> GT
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (BoxE   x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> ord x u
    (DiaI   u    ) -> GT
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (DiaI   x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> ord x u
    (DiaE   u v w) -> GT
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (DiaE   x y z) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> case compare (fromSing x) (fromSing u) of
      EQ -> case ord y v of { EQ -> ord z w ; o -> o }; o -> o
    (UnitRI u    ) -> GT
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (UnitRI x    ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> ord x u
    (UnitRE u v w) -> GT
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (UnitRE x y z) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) ->
      case compare (fromSing x) (fromSing u) of
      { EQ -> case ord y v of { EQ -> ord z w ; o -> o } ; o -> o }
    (IfxRR  u v  ) -> GT
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (IfxRR  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (IfxLR  u v  ) -> GT
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (IfxLR  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (IfxLL  u v  ) -> GT
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (IfxLL  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (IfxRL  u v  ) -> GT
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (IfxRL  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (ExtRR  u v  ) -> GT
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ExtRR  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (ExtLR  u v  ) -> GT
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ExtLR  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (ExtLL  u v  ) -> GT
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ExtLL  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) -> LT
    (ExtLL  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (ExtRL  u v  ) -> GT
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (ExtRL  x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) -> LT
    (ExtLL  u v  ) -> LT
    (ExtRL  u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (DnB    u v  ) -> GT
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (DnB    x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) -> LT
    (ExtLL  u v  ) -> LT
    (ExtRL  u v  ) -> LT
    (DnB    u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (UpB    u v  ) -> GT
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (UpB    x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) -> LT
    (ExtLL  u v  ) -> LT
    (ExtRL  u v  ) -> LT
    (DnB    u v  ) -> LT
    (UpB    u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (DnC    u v  ) -> GT
    (UpC    u v  ) -> GT
ord (DnC    x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) -> LT
    (ExtLL  u v  ) -> LT
    (ExtRL  u v  ) -> LT
    (DnB    u v  ) -> LT
    (UpB    u v  ) -> LT
    (DnC    u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
    (UpC    u v  ) -> GT
ord (UpC    x y  ) uvw = case uvw of
    (Ax          ) -> LT
    (ImpRI  u    ) -> LT
    (ImpRE  u v  ) -> LT
    (ImpLI  u    ) -> LT
    (ImpLE  u v  ) -> LT
    (WithI  u v  ) -> LT
    (WithE1 u    ) -> LT
    (WithE2 u    ) -> LT
    (BoxI   u    ) -> LT
    (BoxE   u    ) -> LT
    (DiaI   u    ) -> LT
    (DiaE   u v w) -> LT
    (UnitRI u    ) -> LT
    (UnitRE u v w) -> LT
    (IfxRR  u v  ) -> LT
    (IfxLR  u v  ) -> LT
    (IfxLL  u v  ) -> LT
    (IfxRL  u v  ) -> LT
    (ExtRR  u v  ) -> LT
    (ExtLR  u v  ) -> LT
    (ExtLL  u v  ) -> LT
    (ExtRL  u v  ) -> LT
    (DnB    u v  ) -> LT
    (UpB    u v  ) -> LT
    (DnC    u v  ) -> LT
    (UpC    u v  ) ->
      case compare (fromSing x) (fromSing u) of { EQ -> ord y v ; o -> o }
