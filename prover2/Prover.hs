module Prover where


import Control.Monad.Supply

import Base
import Match
import Rules


class Fresh a where
  fresh :: a -> Supply String a


instance Fresh Formula where
  fresh (FVar  x ) = supply        >>= \i   -> return (FVar (x ++ i))
  fresh (FOp f xs) = mapM fresh xs >>= \xs' -> return (FOp f xs')

instance Fresh Structure where
  fresh (SVar  x ) = supply        >>= \i   -> return (SVar (x ++ i))
  fresh (SEl   x ) = fresh x       >>= \x'  -> return (SEl x')
  fresh (SOp f xs) = mapM fresh xs >>= \xs' -> return (SOp f xs')

instance Fresh Judgement where
  fresh (Struct x y) = fresh x >>= \x' -> fresh y >>= \y' -> return (Struct x' y')
  fresh (FocusL a y) = fresh a >>= \a' -> fresh y >>= \y' -> return (FocusL a' y')
  fresh (FocusR x b) = fresh x >>= \x' -> fresh b >>= \b' -> return (FocusR x' b')


freshSuffixes :: [String]
freshSuffixes = map show ([1..] :: [Integer])
