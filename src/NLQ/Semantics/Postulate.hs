{-# LANGUAGE GADTs                #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE ScopedTypeVariables  #-}
module NLQ.Semantics.Postulate where


import Control.Monad.Supply (Supply,supply,evalSupply)
import Data.Void (Void)
import Text.Printf (printf)




-- ** Semantic Types/Universe

infixr 4 :*
infixr 2 :->

data E
data T

data Univ (t :: *) where
  E     :: Univ E
  T     :: Univ T
  U     :: Univ ()
  (:->) :: Univ a -> Univ b -> Univ (a -> b)
  (:*)  :: Univ a -> Univ b -> Univ (a  , b)


pattern ET  = E :-> T
pattern EET = E :-> ET
pattern TT  = T :-> T
pattern TTT = T :-> TT
pattern TET = T :-> ET
pattern ETT = E :-> TT


class    UnivI t  where univ :: Univ t
instance UnivI E  where univ = E
instance UnivI T  where univ = T
instance UnivI () where univ = U
instance (UnivI a, UnivI b) => UnivI (a -> b) where univ = univ :-> univ
instance (UnivI a, UnivI b) => UnivI (a  , b) where univ = univ :*  univ


withUniv :: Univ a -> (UnivI a => k) -> k
withUniv (a :-> b) e = withUniv a (withUniv b e)
withUniv (a :*  b) e = withUniv a (withUniv b e)
withUniv U         e = e
withUniv E         e = e
withUniv T         e = e




-- ** Semantic expressions with meaning postulates

infixl 9 :$

type Name = String

data Prim (a :: *) where
  Prim   :: Univ a -> Name -> Prim a
  (:$)   :: Prim (a -> b) -> Expr a -> Prim b
  CaseOf :: Expr (a  , b) -> Expr (b -> a -> c) -> Prim c

type family EXPR (a :: *) where
  EXPR (a -> b) = (Expr a -> Expr b)
  EXPR (a  , b) = (Expr a  , Expr b)
  EXPR ()       = ()
  EXPR E        = Void
  EXPR T        = Bool

data Expr (a :: *) where
  PRIM :: Prim a -> Expr a
  EXPR :: UnivI a => EXPR a -> Expr a




-- ** Type Reconstruction

class TypeOf (f :: * -> *) where
  typeof :: f a -> Univ a

instance TypeOf Prim where
  typeof (Prim t _)   = t
  typeof (f :$ _)     = case typeof f of (_ :-> b)       -> b
  typeof (CaseOf _ f) = case typeof f of (_ :-> _ :-> c) -> c

instance TypeOf Expr where
  typeof (PRIM p) = typeof p
  typeof (EXPR e) = univ



-- * Tiny "Lambda/Logic DSL"

apply :: Expr (a -> b) -> Expr a -> Expr b
EXPR f `apply` x =      (f    x)
PRIM f `apply` x = PRIM (f :$ x)

caseof :: Expr (a  , b) -> Expr (b -> a -> c) -> Expr c
caseof (EXPR (x, y)) (EXPR f) = case f y of { EXPR g -> g x ; PRIM g -> PRIM (g :$ x) }
caseof xy            f        = PRIM (CaseOf xy f)

proj1 :: (UnivI a, UnivI b) => Expr (a , b) -> Expr a
proj1 xy = caseof xy (EXPR(\y -> EXPR(\x -> x)))

proj2 :: (UnivI a, UnivI b) => Expr (a , b) -> Expr b
proj2 xy = caseof xy (EXPR(\y -> EXPR(\x -> y)))

not :: Hask T -> Hask T
not (EXPR(True))  = EXPR(False)
not (EXPR(False)) = EXPR(True)
not x             = Not x

exists :: Univ a -> (Hask a -> Hask T) -> Hask T
exists a f = withUniv a (Exists a (\x -> f (toHask a x)))

forall :: Univ a -> (Hask a -> Hask T) -> Hask T
forall a f = withUniv a (ForAll a (\x -> f (toHask a x)))

infix  6 ≢, ≡
infixr 4 ∧
infixr 2 ⊃

(∧) :: Hask T -> Hask T -> Hask T
EXPR(False) ∧ _           = EXPR(False)
_           ∧ EXPR(False) = EXPR(False)
EXPR(True)  ∧ y           = y
x           ∧ EXPR(True)  = x
x           ∧ y           = x :∧ y

(⊃) :: Hask T -> Hask T -> Hask T
EXPR(False) ⊃ _           = EXPR(True)
EXPR(True)  ⊃ EXPR(True)  = EXPR(True)
EXPR(True)  ⊃ EXPR(False) = EXPR(False)
x           ⊃ y           = x :⊃ y

(≡), (≢) :: Hask E -> Hask E -> Hask T
x ≡ y = x :≡ y
x ≢ y = x :≢ y





-- ** Internalising and externalising expressions

type family Hask t where
  Hask (a -> b) = (Hask a -> Hask b)
  Hask (a  , b) = (Hask a  , Hask b)
  Hask ()       = Expr ()
  Hask E        = Expr E
  Hask T        = Expr T


fromHask :: Univ a -> Hask a -> Expr a
fromHask E          x    = x
fromHask T          x    = x
fromHask U          x    = x
fromHask (a :*  b) (x,y) =
  withUniv a (withUniv b (EXPR(fromHask a x , fromHask b y)))
fromHask (a :-> b)  f    =
  withUniv a (withUniv b (EXPR(\x -> fromHask b (f (toHask a x)))))


toHask :: Univ a -> Expr a -> Hask a
toHask E         x     = x
toHask T         x     = x
toHask U         x     = x
toHask (a :*  b) xy    =
  withUniv a (withUniv b (toHask a (proj1 xy) , toHask b (proj2 xy)))
toHask (a :-> b) f     =
  \x -> toHask b (apply f (fromHask a x))





-- ** Pretty-Printing Expressions

infix  6 :≢, :≡
infixr 4 :∧
infixr 2 :⊃

pattern x :≢ y     = Not (x :≡ y)
pattern x :≡ y     = PRIM (Prim (E :-> E :-> T)   "≡" :$ x :$ y)
pattern Not  x     = PRIM (Prim (T :-> T)         "¬" :$ x)
pattern x :∧ y     = PRIM (Prim (T :-> T :-> T)   "∧" :$ x :$ y)
pattern x :⊃ y     = PRIM (Prim (T :-> T :-> T)   "⊃" :$ x :$ y)
pattern ForAll t f = PRIM (Prim ((t :-> T) :-> T) "∀" :$ EXPR f)
pattern Exists t f = PRIM (Prim ((t :-> T) :-> T) "∃" :$ EXPR f)

instance Show (Expr t) where
  showsPrec d x = evalSupply (pp2 d x) ns
    where
    ns :: [Name]
    ns = [ x | n <- [0..], let x = 'x':show n ]

    infixr 9 <.>

    (<.>) :: Supply Name ShowS -> Supply Name ShowS -> Supply Name ShowS
    s1 <.> s2 = do s1' <- s1; s2' <- s2; return (s1' . s2')

    showStr :: String -> Supply Name ShowS
    showStr str = return (showString str)

    showChr :: Char -> Supply Name ShowS
    showChr chr = return (showChar chr)

    pp1 :: Int -> Prim a -> Supply Name ShowS
    pp1 d (Prim _ n)    = showStr n
    pp1 d (f :$ x)      = showParen (d > 10) <$> pp1 10 f <.> showChr ' ' <.> pp2 11 x
    pp1 d (CaseOf xy f) = do
      x <- supply
      y <- supply
      case typeof xy of
        (a :* b) -> do
          let fxy = (f `apply` (PRIM(Prim b y))) `apply` (PRIM(Prim a x))
          showParen (d > 1) <$>
            showStr "case " <.> pp2 0 xy <.> showStr (printf " of (%s,%s) → " x y) <.> pp2 2 fxy

    pp2 :: Int -> Expr a -> Supply Name ShowS
    pp2 d (Not (Exists a f)) = do
      x <- supply
      showParen (d > 1) <$> showStr (printf "∄%s." x) <.> pp2 2 (f (PRIM(Prim a x)))
    pp2 d (ForAll a f)       = do
      x <- supply
      showParen (d > 1) <$> showStr (printf "∀%s." x) <.> pp2 2 (f (PRIM(Prim a x)))
    pp2 d (Exists a f)       = do
      x <- supply
      showParen (d > 1) <$> showStr (printf "∃%s." x) <.> pp2 2 (f (PRIM(Prim a x)))
    pp2 d (u :≢ v) = showParen (d > 6) <$> pp2 7 u <.> showStr " ≢ " <.> pp2 7 v
    pp2 d (u :≡ v) = showParen (d > 6) <$> pp2 7 u <.> showStr " ≡ " <.> pp2 7 v
    pp2 d (u :∧ v) = showParen (d > 2) <$> pp2 3 u <.> showStr " ∧ " <.> pp2 2 v
    pp2 d (u :⊃ v) = showParen (d > 4) <$> pp2 5 u <.> showStr " ⊃ " <.> pp2 4 v
    pp2 d (Not  u) = showParen (d > 8) <$> showStr "¬ " <.> pp2 4 u
    pp2 d (PRIM f) = pp1 d f
    pp2 d (EXPR f :: Expr a) = pp3 d (univ :: Univ a) f

    pp3 :: Int -> Univ a -> EXPR a -> Supply Name ShowS
    pp3 d (a :-> b) f       = do
      x <- supply
      showParen (d > 1) <$> showStr (printf "λ%s." x) <.> pp2 d (f (PRIM (Prim a x)))
    pp3 d (a :*  b) (x , y) = showParen True <$> pp2 0 x <.> showChr ',' <.> pp2 0 y
    pp3 d U         ()      = showStr "()"

-- -}
-- -}
-- -}
-- -}
-- -}
