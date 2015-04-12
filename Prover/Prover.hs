{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses, DeriveGeneric #-}
module Prover where


import           Control.Monad (zipWithM_)
import           Control.Applicative ((<$>))
import           Control.DeepSeq (NFData)
import           Control.Monad.State
import qualified Data.HashSet as S
import           Data.IntMap (IntMap,(!))
import qualified Data.IntMap as IM
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe (mapMaybe)
import           Data.Void (Void)
import           Data.Hashable
import           GHC.Generics

data Term c v where
  Var :: ! v               -> Term c v
  Con :: ! c -> [Term c v] -> Term c v
  deriving (Eq,Ord,Generic)


instance (Hashable c, Hashable v) => Hashable (Term c v)
instance (NFData   c, NFData   v) => NFData (Term c v)


type VarId     = String
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


data Rule r c v = Rule
  { name       :: ! r
  , guard      :: Term c Void -> Bool
  , arity      :: ! Int
  , premises   :: ! [Term c v]
  , conclusion :: ! (Term c v)
  }


infixr 1 ⟶

(⟶) :: [Term c VarId] -> Term c VarId -> r -> Rule r c Int
(⟶) ps c n = Rule n (const True) (length ps) ps' c'
  where

    (c' : ps') = evalState (mapM lbl (c : ps)) (0, M.empty)

    lbl (Var x) = do (i, vm) <- get
                     case M.lookup x vm of
                      Just j -> return (Var j)
                      _      -> do put (i + 1, M.insert x i vm); return (Var i)
    lbl (Con x xs) = fmap (Con x) (mapM lbl xs)

instance (Show r, Show c, Show v, Show (Term c v)) => Show (Rule r c v) where
  showsPrec _ (Rule n _ _ ps c) =
    showParen True (showList ps . showString " ⟶ " . shows c) . showChar ' ' . shows n


-- TODO: perhaps `xs` has to be reversed
build :: r -> Int -> [Term r Void] -> [Term r Void]
build n a ts = let (xs,ys) = splitAt a ts in Con n xs : ys


-- |Apply the given variable map to a given term. Note: the variable
--  map has to contain a term for every variable used in the given
--  term. The resulting term will be variable-free.
subst :: VMap c -> Term c Int -> Term c Void
subst s = app where

  app (Con x xs) = Con x (map app xs)
  app (Var i   ) = s ! i


-- |Search for proofs of the given goal using the gives rules using
--  breadth-first search.
--  Note: this algorithm performs loop-checking under the assumption
--  that /unary/ rules may cause loops, and rules of higher arity
--  make progress.
findAll :: (Hashable c, Ord c) => Term c Void -> [Rule r c Int] -> [Term r Void]
findAll goal rules = slv [(S.empty,[goal],head)] []
  where
    slv [                    ] [ ] = []
    slv [                    ] acc = slv (reverse acc) []
    slv ((_   ,  [],prf):prfs) acc = prf [] : slv prfs acc
    slv ((seen,g:gs,prf):prfs) acc
      | S.member g seen = slv prfs acc
      | otherwise       = slv prfs (mapMaybe step rules ++ acc)
      where
        step (Rule n canApply a ps c)
          | canApply g = (\sb -> (seen', map (subst sb) ps ++ gs, prf')) <$> execInst (inst g c)
          | otherwise  = Nothing
          where
            prf'  = prf . build n a
            seen' | a == 1    = S.insert g seen
                  | otherwise = S.empty



verify :: (Show (Term c Void), Show (Term c Int), Eq c) => [Rule String c Int] -> Term c Void -> Term String Void -> IO ()
verify rules = vrf
  where
    rmp = M.fromList (zip (map name rules) rules)
    vrf goal (Con n args) =
      case M.lookup n rmp of
       Nothing -> error ("verify: no rule named '"++n++"'")
       Just (Rule _ canApply a ps c) ->
         if not (canApply goal)
         then error ("verify: '"++n++"' cannot apply to '"++show goal++"'")
         else case execInst (inst goal c) of
               Nothing -> error ("verify: cannot instantiate '"++show c++"' to '"++show goal++"'")
               Just sb ->
                 if a /= length ps
                 then error ("verify: wrong number of arguments")
                 else zipWithM_ vrf (map (subst sb) ps) args
