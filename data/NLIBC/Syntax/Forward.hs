{-# LANGUAGE TemplateHaskell, QuasiQuotes, FlexibleInstances, FlexibleContexts,
    TypeFamilies, GADTs, TypeOperators, DataKinds, PolyKinds, RankNTypes,
    KindSignatures, UndecidableInstances, StandaloneDeriving, PatternSynonyms,
    AllowAmbiguousTypes, MultiParamTypeClasses, FunctionalDependencies,
    ViewPatterns, ScopedTypeVariables, TupleSections #-}
module NLIBC.Syntax.Forward where


import NLIBC.Syntax.Base
import Control.Arrow ((***))
import Control.Applicative (empty)
import Data.Function (on)
import Data.Maybe (mapMaybe)
import Data.List (sort)
import Data.List.Ordered (insertBag,merge,mergeAll,has,minus,subset,nubSort)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Singletons.Decide
import Data.Singletons.Prelude
import qualified Debug.Trace as D (trace)


-- TODO: in order to accommodate additive types, we need to extend
-- this framework by returning choices of atomic types, and consuming
-- those at the same time during proof search.


data Typed where
  Typed :: SSequent s -> Syn s -> Typed

instance Show Typed where
  show (Typed _ x) = show x

instance Eq Typed where
  Typed t1 x1 == Typed t2 x2 =
    case t1 %~ t2 of
    { Proved Refl -> x1 == x2 ; _ -> False }

instance Ord Typed where
  Typed t1 x1 `compare` Typed t2 x2 =
    case fromSing t1 `compare` fromSing t2 of
    { EQ -> forget x1 `compare` forget x2 ; o -> o }

data TypedBy (xs :: [Type]) (b :: Type) where
  TypedBy :: SStructI x -> ToList x :~: xs -> Syn (x :⊢ StO b) -> TypedBy xs y

instance Show (TypedBy xs b) where
  show (TypedBy _ _ f) = show f


-- * Top-Down Proof Search

type PartialProof = ([Type],[Typed])

topDown :: SList (xs :: [Type]) -> SType b -> [TypedBy xs b]
topDown sxs sb = case setup sxs sb of
  Nothing -> []
  Just pp -> mapMaybe (check sxs sb) (search [pp])
  where
  setup :: SList (xs :: [Type]) -> SType b -> Maybe PartialProof
  setup sxs sb =
    if isBalanced (as,bs) then Just (ts2,xs0) else Nothing
    where
      complex (El _) = False
      complex _      = True
      ts0     = map (True,) (fromSing sxs) ++ [(False,fromSing sb)]
      ts1     = subformulas (map snd ts0)
      ts2     = filter complex ts1
      (as,bs) = allAtoms ts0
      xs0     = sort (allAxioms as)

  check :: SList xs -> SType b -> Typed -> Maybe (TypedBy xs b)
  check xs1 b1 (Typed (x :%⊢ SStO b2) f) =
    case b1 %~ b2 of
    Disproved _ -> Nothing ; Proved Refl ->
      case toList x of
      Nothing  -> Nothing ; Just xs2 ->
        case xs2 %~ xs1 of
        Disproved _ -> Nothing ; Proved Refl -> Just (TypedBy x Refl f)
  check _ _ _ = Nothing

  search :: [PartialProof] -> [Typed]
  search []  = []
  search in0 = out ++ search in1
    where
      out = map (head . snd) (filter ((==1).length) in0)
      in1 = nubSort (concatMap fun1 in0 ++ concatMap fun2 in0)

      fun1 :: PartialProof -> [PartialProof]
      fun1 (ts0,xs0) = do
        f                   <- [unfR,unfL,focR,focL,impRR,impLR
                               ,res11,res12,res13,res14,qrR'
                               ,diaL,diaR,boxL,boxR,res21,res22
                               ,ifxRR,ifxLR,ifxLL,ifxRL
                               ,extRR,extLR,extLL,extRL]
        x1                  <- xs0     ; let xs1 = xs0 `minus` [x1]
        (ts1,x@(Typed s _)) <- f x1    ; let xs2 = insertBag x xs1

        let ts2 = ts0 `minus` ts1
        if not (ts1 `subset` ts0) then empty else return (ts2,xs2)

      fun2 :: PartialProof -> [PartialProof]
      fun2 (ts0,xs0) = do
        f                   <- [impRL,impLL,qrL']
        x1                  <- xs0     ; let xs1 = xs0 `minus` [x1]
        x2                  <- xs1     ; let xs2 = xs1 `minus` [x2]
        (ts1,x@(Typed s _)) <- f x1 x2 ; let xs3 = insertBag x xs2

        let ts2 = ts0 `minus` ts1
        if not (ts1 `subset` ts0) then empty else return (ts2,xs3)

      unfR,unfL,focR,focL :: Typed -> [([Type],Typed)]
      unfR (Typed (x :%⊢ SStO b) f) = case pol b of
        Left  p -> empty
        Right n -> return ([],Typed (x :%⊢> b) (UnfR n f))
      unfR _ = empty
      unfL (Typed (SStI a :%⊢ y) f) = case pol a of
        Left  p -> return ([],Typed (a :%<⊢ y) (UnfL p f))
        Right n -> empty
      unfL _ = empty
      focR (Typed (x :%⊢> b) f) = case pol b of
        Left  p -> return ([],Typed (x :%⊢ SStO b) (FocR p f))
        Right n -> empty
      focR _ = empty
      focL (Typed (a :%<⊢ y) f) = case pol a of
        Left  p -> empty
        Right n -> return ([],Typed (SStI a :%⊢ y) (FocL n f))
      focL _ = empty

      impRL,impLL :: Typed -> Typed -> [([Type],Typed)]
      impRL (Typed (x :%⊢> a) f) (Typed (b :%<⊢ y) g) =
        forEach [Solid,Hollow] $ \k ->
        let t = SImpR k a b in ([fromSing t],Typed (t :%<⊢ SIMPR k x y) (ImpRL f g))
      impRL _ _ = empty
      impLL (Typed (x :%⊢> a) f) (Typed (b :%<⊢ y) g) =
        forEach [Solid,Hollow] $ \k ->
        let t = SImpL k b a in ([fromSing t],Typed (t :%<⊢ SIMPL k y x) (ImpLL f g))
      impLL _ _ = empty

      impRR,impLR :: Typed -> [([Type],Typed)]
      impRR (Typed (x :%⊢ SIMPR k (SStI a) (SStO b)) f) =
        let t = SImpR k a b in
        return ([fromSing t],Typed (x :%⊢ SStO t) (ImpRR f))
      impRR _ = empty
      impLR (Typed (x :%⊢ SIMPL k (SStO b) (SStI a)) f) =
        let t = SImpL k b a in
        return ([fromSing t],Typed (x :%⊢ SStO t) (ImpLR f))
      impLR _ = empty

      res11,res12,res13,res14 :: Typed -> [([Type],Typed)]
      res11 (Typed (y :%⊢ SIMPR k x z) (Res12 _)) = empty
      res11 (Typed (y :%⊢ SIMPR k x z) f)         =
        return ([],Typed (SPROD k x y :%⊢ z) (Res11 f))
      res11 _                                     = empty
      res12 (Typed (SPROD k x y :%⊢ z) (Res11 _)) = empty
      res12 (Typed (SPROD k x y :%⊢ z) f)         =
        return ([],Typed (y :%⊢ SIMPR k x z) (Res12 f))
      res12 _                                     = empty
      res13 (Typed (x :%⊢ SIMPL k z y) (Res14 _)) = empty
      res13 (Typed (x :%⊢ SIMPL k z y) f)         =
        return ([],Typed (SPROD k x y :%⊢ z) (Res13 f))
      res13 _                                     = empty
      res14 (Typed (SPROD k x y :%⊢ z) (Res13 _)) = empty
      res14 (Typed (SPROD k x y :%⊢ z) f)         =
        return ([],Typed (x :%⊢ SIMPL k z y) (Res14 f))
      res14 _                                     = empty

      qrL' :: Typed -> Typed -> [([Type],Typed)]
      qrL' (Typed (sig :%⊢> b) f) (Typed (c :%<⊢ y) g) = case sFollow sig of
        Nothing             -> empty
        Just (Trail x Refl) ->
          let t = SQR (c :%⇦ b) in
          return ([fromSing t],Typed (sPlug x (SStI t) :%⊢ y) (qrL x f g))
      qrL' _ _ = empty
      qrR' :: Typed -> [([Type],Typed)]
      qrR' (Typed (sig :%⊢ SStO b) f) = concatMap go (sFocus sig)
        where
          go (Focus x (SStI a) Refl) =
            let t = a :%⇨ b in
            return ([fromSing t],Typed (sTrace x :%⊢ SStO t) (qrR x f))
          go _ = empty
      qrR' _ = empty

      diaL,diaR,boxL,boxR :: Typed -> [([Type],Typed)]
      diaL (Typed (SDIA k (SStI a) :%⊢ y) f) =
        let t = SDia k a in return ([fromSing t],Typed (SStI t :%⊢ y) (DiaL f))
      diaL _                                 = empty
      diaR (Typed (x :%⊢> b) f)              =
        forEach [Reset,Infixate,Extract] $ \k ->
        let t = SDia k b in ([fromSing t],Typed (SDIA k x :%⊢> t) (DiaR f))
      diaR _                                 = empty
      boxL (Typed (a :%<⊢ y) f)              =
        forEach [Reset,Infixate,Extract] $ \k ->
        let t = SBox k a in ([fromSing t],Typed (t :%<⊢ SBOX k y) (BoxL f))
      boxL _                                 = empty
      boxR (Typed (x :%⊢ SBOX k (SStO b)) f) =
        let t = SBox k b in return ([fromSing t],Typed (x :%⊢ SStO t) (BoxR f))
      boxR _                                 = empty

      res21,res22 :: Typed -> [([Type],Typed)]
      res21 (Typed (x :%⊢ SBOX k y) (Res22 _)) = empty
      res21 (Typed (x :%⊢ SBOX k y) f)         =
        return ([],Typed (SDIA k x :%⊢ y) (Res21 f))
      res21 _                                  = empty
      res22 (Typed (SDIA k x :%⊢ y) (Res21 _)) = empty
      res22 (Typed (SDIA k x :%⊢ y) f)         =
        return ([],Typed (x :%⊢ SBOX k y) (Res22 f))
      res22 _                                  = empty

      ifxRR,ifxLR,ifxLL,ifxRL :: Typed -> [([Type],Typed)]
      ifxRR (Typed ((x :%∙ y) :%∙ SIFX z :%⊢ w) f) =
        return ([],Typed (x :%∙ (y :%∙ SIFX z) :%⊢ w) (IfxRR f))
      ifxRR _ = empty
      ifxLR (Typed ((x :%∙ y) :%∙ SIFX z :%⊢ w) f) =
        return ([],Typed ((x :%∙ SIFX z) :%∙ y :%⊢ w) (IfxLR f))
      ifxLR _ = empty
      ifxLL (Typed (SIFX z :%∙ (y :%∙ x) :%⊢ w) f) =
        return ([],Typed ((SIFX z :%∙ y) :%∙ x :%⊢ w) (IfxLL f))
      ifxLL _ = empty
      ifxRL (Typed (SIFX z :%∙ (y :%∙ x) :%⊢ w) f) =
        return ([],Typed (y :%∙ (SIFX z :%∙ x) :%⊢ w) (IfxRL f))
      ifxRL _ = empty

      extRR,extLR,extLL,extRL :: Typed -> [([Type],Typed)]
      extRR (Typed (x :%∙ (y :%∙ SEXT z) :%⊢ w) f) =
       return ([],Typed ((x :%∙ y) :%∙ SEXT z :%⊢ w) (ExtRR f))
      extRR _ = empty
      extLR (Typed ((x :%∙ SEXT z) :%∙ y :%⊢ w) f) =
       return ([],Typed ((x :%∙ y) :%∙ SEXT z :%⊢ w) (ExtLR f))
      extLR _ = empty
      extLL (Typed ((SEXT z :%∙ y) :%∙ x :%⊢ w) f) =
       return ([],Typed (SEXT z :%∙ (y :%∙ x) :%⊢ w) (ExtLL f))
      extLL _ = empty
      extRL (Typed (y :%∙ (SEXT z :%∙ x) :%⊢ w) f) =
       return ([],Typed (SEXT z :%∙ (y :%∙ x) :%⊢ w) (ExtRL f))
      extRL _ = empty


-- * Helper functions

forEach :: [Kind] -> (forall k. SKind k -> a) -> [a]
forEach ks f = map (\k -> withKind k f) ks
  where
    withKind :: Kind -> (forall k. SKind k -> a) -> a
    withKind Solid    f = f SSolid
    withKind Hollow   f = f SHollow
    withKind Reset    f = f SReset
    withKind Infixate f = f SInfixate
    withKind Extract  f = f SExtract

-- |Concatenate a pair of lists pointwise.
pconcat :: ([a],[b]) -> ([a],[b]) -> ([a],[b])
pconcat (x1,y1) (x2,y2) = (x1++x2, y1++y2)

-- |List all positive and negative occurrences in a type.
atoms :: Bool -> Type -> ([Atom],[Atom])
atoms p@True  (El a)        = ([a],[])
atoms p@False (El a)        = ([],[a])
atoms p       (Dia   _ a)   = atoms p a
atoms p       (Box   _ a)   = atoms p a
atoms p       (UnitR _ a)   = atoms p a
atoms p       (ImpR  _ a b) = pconcat (atoms (not p) a) (atoms p b)
atoms p       (ImpL  _ b a) = pconcat (atoms p b) (atoms (not p) a)

-- |List all positive and negative occurrences in a list of types.
allAtoms :: [(Bool,Type)] -> ([Atom],[Atom])
allAtoms = (concat *** concat) . unzip . map (uncurry atoms)

-- |Check if a list of expressions is balanced, i.e. if it could ever
--  produce a proof.
isBalanced :: ([Atom],[Atom]) -> Bool
isBalanced = uncurry (==) . (sort *** sort)

-- |Create a set of axioms, one for every positive/negative pair of
--  atoms.
allAxioms :: [Atom] -> [Typed]
allAxioms as = map go as
  where
    go :: Atom -> Typed
    go S   = Typed (SEl SS   :%<⊢ SStO (SEl SS  )) (AxL Neg_El)
    go N   = Typed (SEl SN   :%<⊢ SStO (SEl SN  )) (AxL Neg_El)
    go NP  = Typed (SEl SNP  :%<⊢ SStO (SEl SNP )) (AxL Neg_El)
    go PP  = Typed (SEl SPP  :%<⊢ SStO (SEl SPP )) (AxL Neg_El)
    go INF = Typed (SEl SINF :%<⊢ SStO (SEl SINF)) (AxL Neg_El)


-- |List all sub-formulas in a type in ascending order.
class Subformulas a where
  subformulas :: a -> [Type]

instance Subformulas Type where
  subformulas a            = insertBag a (go a)
    where
      go (El _)            = []
      go (Dia   _ a)       = subformulas a
      go (Box   _ a)       = subformulas a
      go (UnitR _ a)       = subformulas a
      go (ImpR  _ a b)     = subformulas a `merge` subformulas b
      go (ImpL  _ b a)     = subformulas b `merge` subformulas a

instance Subformulas StructI where
  subformulas (StI    a)   = subformulas a
  subformulas (DIA  _ x)   = subformulas x
  subformulas (PROD _ x y) = subformulas x `merge` subformulas y
  subformulas _            = []

instance Subformulas StructO where
  subformulas (StO    a)   = subformulas a
  subformulas (BOX  _ x)   = subformulas x
  subformulas (IMPL _ y x) = subformulas y `merge` subformulas x
  subformulas (IMPR _ x y) = subformulas x `merge` subformulas y

instance Subformulas Sequent where
  subformulas (x :⊢  y)    = subformulas x `merge` subformulas y
  subformulas (x :⊢> b)    = subformulas x `merge` subformulas b
  subformulas (a :<⊢ y)    = subformulas a `merge` subformulas y

instance Subformulas Typed where
  subformulas (Typed ss _) = subformulas (fromSing ss)

instance Subformulas a => Subformulas [a] where
  subformulas = mergeAll . map subformulas


{-
data TypedBy (xs :: [Type]) (b :: Type) where
     TypedBy :: SStructI x -> ToList x :~: xs -> Syn (x :⊢ b) -> TypedBy xs y

instance Show (TypedBy xs b) where
  show (TypedBy _ _ f) = show f
-}

-- -}
-- -}
-- -}
-- -}
-- -}
