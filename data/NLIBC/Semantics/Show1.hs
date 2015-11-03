{-# LANGUAGE DataKinds, KindSignatures #-}
module NLIBC.Semantics.Show1 (show1) where


import Prelude hiding ((!!))
import Control.Monad.State
import Data.Singletons (fromSing)
import NLIBC.Syntax (Prf(..))
import NLIBC.Semantics (Sem(..),eta,(!!))
import Text.Printf (printf)


type VS a = State ([String],[String]) a

newtype Str (ts :: [*]) (t :: *) = Str { runStr :: VS String }


instance Sem Str where
  var  n   = Str $ do (env,_) <- get
                      return (env !! fromSing n)
  abs  f   = Str $ do (env,x:xs) <- get
                      put (x:env,xs)
                      f' <- runStr f
                      (x:env,xs) <- get
                      put (env,xs)
                      return (printf "(λ%s.%s)" x f')
  app  f x = Str $ printf "(%s %s)" <$> runStr f <*> runStr x
  top      = Str $ return "()"
  pair x y = Str $ printf "(%s, %s)" <$> runStr x <*> runStr y
  p1   x   = Str $ printf "(π₁ %s)" <$> runStr x
  p2   x   = Str $ printf "(π₂ %s)" <$> runStr x


show1 :: [String] -> Prf s -> String
show1 boundVars x = evalState (runStr (eta x)) (boundVars,freeVars)
  where
    freeVars = map (('x':) . show) [1..]
