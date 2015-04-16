{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, UndecidableInstances, DeriveGeneric #-}
module Logic.Prover (Term(..),Rule(..),mkRule,findAll,findFirst) where


import           Control.DeepSeq (NFData)
import           Control.Monad.State
import qualified Data.HashSet as S
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Void (Void)
import           Data.Hashable
import           GHC.Generics
import           Debug.Trace (trace)


data Term c v where
  Var :: ! v               -> Term c v
  Con :: ! c -> [Term c v] -> Term c v
  deriving (Eq,Ord,Generic)


instance (Hashable c, Hashable v) => Hashable (Term c v)
instance (NFData   c, NFData   v) => NFData (Term c v)


instance (Show v) => Show (Term String v) where
  showsPrec _ (Var i)    = shows i
  showsPrec _ (Con f []) = showString f
  showsPrec p (Con f xs) =
    showParen (p >= 1) $ showString f . showSeq (showsPrec 1) xs
    where
      showSeq _  []     = id
      showSeq ss (x:xs) = showChar ' ' . ss x . showSeq ss xs


type VMap  c   = IntMap (Term c Void)
type Inst  c a = StateT (VMap c) Maybe a


execInst :: Inst c a -> Maybe (VMap c)
execInst x = execStateT x IM.empty


inst :: (Eq c) => Term c Void -> Term c Int -> Inst c (Term c Void)
inst   (Con x xs) (Con y ys) | x == y = liftM (Con x) (instAll xs ys)
inst x@(Con _ _ ) (Var i   )          = do vm <- get
                                           case IM.lookup i vm of
                                            Just y -> if x == y
                                                      then return x
                                                      else fail "cannot instantiate"
                                            _      -> do put (IM.insert i x vm)
                                                         return x
inst _            _                   = fail "cannot instantiate"


instAll :: (Eq c) => [Term c Void] -> [Term c Int] -> Inst c [Term c Void]
instAll    []     []  = return []
instAll (x:xs) (y:ys) = liftM2 (:) (inst x y) (instAll xs ys)
instAll  _      _     = fail "cannot instantiate"


type RuleId = String

data Rule c v = Rule
  { name       :: ! RuleId
  , guard      :: Term c Void -> Bool
  , arity      :: ! Int
  , premises   :: ! [Term c v]
  , conclusion :: ! (Term c v)
  }

mkRule :: [Term c String] -> Term c String -> RuleId -> Rule c Int
mkRule ps c n = Rule n (const True) (length ps) ps' c'
  where

    (c' : ps') = evalState (mapM lbl (c : ps)) (0, M.empty)

    lbl (Var x) = do (i, vm) <- get
                     case M.lookup x vm of
                      Just j -> return (Var j)
                      _      -> do put (i + 1, M.insert x i vm); return (Var i)
    lbl (Con x xs) = fmap (Con x) (mapM lbl xs)


instance (Show c, Show v, Show (Term c v)) => Show (Rule c v) where
  showsPrec _ (Rule n _ _ ps c) =
    showParen True (showList ps . showString " ⟶ " . shows c) . showChar ' ' . showString n


build :: r -> Int -> [Term r Void] -> [Term r Void]
build n a ts = let (xs,ys) = splitAt a ts in Con n xs : ys


-- |Apply the given variable map to a given term. Note: the variable
--  map has to contain a term for every variable used in the given
--  term. The resulting term will be variable-free.
subst :: VMap c -> Term c Int -> Maybe (Term c Void)
subst s = app where

  app (Con x xs) = Con x <$> mapM app xs
  app (Var i   ) = IM.lookup i s


-- |Search for proofs of the given goal using the gives rules using
--  breadth-first search.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
findAll :: (Hashable c, Ord c) => Term c Void -> [Rule c Int] -> [Term String Void]
findAll goal rules = slv [(S.empty,[goal],head)] []
  where
    slv [                    ] [ ] = []
    slv [                    ] acc = slv (reverse acc) []
    slv ((_   ,  [],prf):prfs) acc = prf [] : slv prfs acc
    slv ((seen,g:gs,prf):prfs) acc
      | S.member g seen = slv prfs acc
      | otherwise       = slv prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n canApply a ps c) =
          if canApply g
          then do sb <- execInst (inst g c)
                  let prf'  = prf . build n a
                  let seen' | a == 1    = S.insert g seen
                            | otherwise = S.empty
                  case mapM (subst sb) ps of
                   Just ps' -> return (seen', ps' ++ gs, prf')
                   Nothing  -> error ("Free variable in substitution for rule `"++n++"'.")
          else fail ("Cannot apply rule `"++n++"'")


-- |Search for proofs of the given goal using the gives rules using
--  depth-limited breadth-first search.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of other arities
--  make progress.
findFirst :: (Hashable c, Ord c)
          => Int           -- ^ Search Depth
          -> [Term c Void] -- ^ Goal Terms
          -> [Rule c Int]  -- ^ Inference rules
          -> [(Term c Void, Term String Void)]
findFirst d goals rules = slv d (map (\g -> (S.empty,g,[g],head)) goals) []
  where
    slv 0                        _   _ = []
    slv d [                      ] [ ] = []
    slv d [                      ] acc = slv (d - 1) (reverse acc) []
    slv d ((_   ,o,  [],prf):_   ) _   = [(o, prf [])]
    slv d ((seen,o,g:gs,prf):prfs) acc
      | S.member g seen = slv d prfs acc
      | otherwise       = slv d prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n canApply a ps c) =
          if canApply g
          then do sb <- execInst (inst g c)
                  let prf'  = prf . build n a
                  let seen' | a == 1    = S.insert g seen
                            | otherwise = S.empty
                  case mapM (subst sb) ps of
                   Just ps' -> return (seen', o, ps' ++ gs, prf')
                   Nothing  -> error ("Free variable in substitution for rule `"++n++"'.")
          else fail ("Cannot apply rule `"++n++"'")
