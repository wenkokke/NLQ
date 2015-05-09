module CG.Prover.Ins (Ins,runIns,ins) where


import Control.Monad.State (MonadState(..),StateT,execStateT,liftM,liftM2)
import Data.IntMap as IM (lookup,empty,insert)
import Data.Void (Void)
import CG.Prover.Base


type Ins c a = StateT (VMap c Void) Maybe a


runIns :: Ins c a -> Maybe (VMap c Void)
runIns x = execStateT x IM.empty


ins :: (Eq c) => Term c Void -> Term c Int -> Ins c (Term c Void)
ins   (Con x xs) (Con y ys) | x == y = liftM (Con x) (insAll xs ys)
ins x@(Con _ _ ) (Var i   )          = do vm <- get
                                          case IM.lookup i vm of
                                           Just y -> if x == y
                                                     then return x
                                                     else fail "cannot insantiate"
                                           _      -> do put (IM.insert i x vm)
                                                        return x
ins _            _                   = fail "cannot insantiate"


insAll :: (Eq c) => [Term c Void] -> [Term c Int] -> Ins c [Term c Void]
insAll    []     []  = return []
insAll (x:xs) (y:ys) = liftM2 (:) (ins x y) (insAll xs ys)
insAll  _      _     = fail "cannot instantiate"
