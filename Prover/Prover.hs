{-# LANGUAGE GADTs, FlexibleInstances, FlexibleContexts, MultiParamTypeClasses #-}
module Prover where


import           Control.Monad.State
import           Data.IntMap (IntMap,(!))
import qualified Data.IntMap as IM
import qualified Data.Map as M
import           Data.Void (Void)


data Term c v where
  Var :: ! v               -> Term c v
  Con :: ! c -> [Term c v] -> Term c v
  deriving (Eq)


type VarId     = String
type VMap  c   = IntMap (Term c Void)
type Inst  c a = StateT (VMap c) Maybe a


runInst :: Inst c a -> Maybe (a, VMap c)
runInst x = runStateT x IM.empty


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


mkProof :: r -> Int -> [Term r Void] -> [Term r Void]
mkProof n a ts = let (xs,ys) = splitAt a ts in Con n xs : ys


-- |Apply the given variable map to a given term. Note: the variable
--  map has to contain a term for every variable used in the given
--  term. The resulting term will be variable-free.
apply :: VMap c -> Term c Int -> Term c Void
apply s = app where

  app (Con x xs) = Con x (map app xs)
  app (Var i   ) = s ! i


-- |Search for proofs of the given goal using the gives rules using
--  depth-limited depth-first search.
searchToDepth :: (Eq c) => Int -> Term c Void -> [Rule r c Int] -> [Term r Void]
searchToDepth d g rs = slv (d + 1) [g] head where

    slv 0        _ _ = []
    slv _ [      ] p = [p []]
    slv d (g : gs) p = concatMap step rs where

      step (Rule n grd a ps c)
        | grd g =
            case runInst (inst g c) of
            Just (_, s) -> slv (d - 1) (map (apply s) ps ++ gs) (p . mkProof n a)
            Nothing     -> []
        | otherwise = []


-- |Search for proofs of the given goal using the gives rules using
--  iterative deepening depth-first search.
search :: (Eq c) => Term c Void -> [Rule r c Int] -> [Term r Void]
search g rs = sch 1 where

    sch d = if null here then next else here where

        here = searchToDepth d g rs
        next = sch (d + 1)
