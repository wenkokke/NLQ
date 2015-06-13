{-# LANGUAGE GADTs, RankNTypes, FlexibleInstances, FlexibleContexts,
    UndecidableInstances, DeriveGeneric, DeriveFunctor, DeriveFoldable,
    DeriveTraversable, StandaloneDeriving, RecordWildCards #-}
module CG.Prover.Base where


import Control.Monad.State (MonadState(..),evalState)
import Control.DeepSeq     (NFData)
import Data.Char           (ord)
import Data.Hashable       (Hashable)
import Data.Serialize      (Serialize)
import Data.IntMap as IM   (IntMap,lookup,empty,insert)
import Data.List           (intersperse)
import Data.Void           (Void,absurd)
import Data.Void.Unsafe    (unsafeVacuous)
import GHC.Generics        (Generic)


-- * Special Show instance for String

class    ToString a      where toString :: a -> String
instance ToString Bool   where toString = (++" ") . show
instance ToString Int    where toString = (++" ") . show
instance ToString Void   where toString = absurd
instance ToString String where toString = (++" ")
instance ToString Char   where toString = (:" ")


-- * Terms

data Term c v where
  Var :: ! v               -> Term c v
  Con :: ! c -> [Term c v] -> Term c v
  deriving (Eq,Ord,Generic)


deriving instance Functor     (Term c)
deriving instance Foldable    (Term c)
deriving instance Traversable (Term c)
instance (Hashable  c, Hashable  v) => Hashable  (Term c v)
instance (NFData    c, NFData    v) => NFData    (Term c v)
instance (Serialize c, Serialize v) => Serialize (Term c v)


-- |A class which defines a printable operator. The @prec@ function
--  returns the precedence of the operator. The @template@ function
--  is a generalisation of the fixity, where the operator can be
--  anything that knows how to print itself.
class Operator a where
  prec     :: a -> Int
  template :: a -> ([ShowS] -> ShowS)


instance Operator String where
  prec     _    = 0
  template x [] = showString x
  template x xs =
    showParen True (foldr (.) id (intersperse (showChar ' ') (showString x : xs)))


instance (Operator c, ToString v) => Show (Term c v) where
  showsPrec _ (Var i)    =
    showString (toString i)
  showsPrec p (Con x xs)
    | p > 0 && q > 0 && p >= q = showString "( " . ret . showString ") "
    | otherwise                = ret
    where
      q   = prec x
      ret = template x (map (showsPrec q) xs)


-- * Guards

class (Eq c) => Guardable c where
  isAtomic   :: Term c v -> Bool
  isPositive :: Term c v -> Bool
  isNegative :: Term c v -> Bool


data Guard c
  = Any
  | Atomic   (Term c Bool)
  | Positive (Term c Bool)
  | Negative (Term c Bool)
  | And (Guard c) (Guard c)
  deriving (Eq,Ord,Show,Generic)


instance (Hashable  c) => Hashable  (Guard c)
instance (NFData    c) => NFData    (Guard c)
instance (Serialize c) => Serialize (Guard c)


-- |Construct a given primitive guard, together with its arguments, into a
--  guarding function. Used internally in @runGuard@.
mkGuard :: (Guardable c)
           => (forall v'. Term c v' -> Bool)
           -> Term c Bool
           -> (forall v'. Term c v' -> Bool)
mkGuard _      _     (Var _)             = True
mkGuard p (Var True)      y              = p y
mkGuard _ (Var _   )      _              = True
mkGuard p (Con x xs) (Con y ys) | x == y = and (zipWith (mkGuard p) xs ys)
mkGuard _      _          _              = False


-- |Run a guard, checking if the given Term has all the desired properties.
runGuard :: (Guardable c) => Guard c -> (forall v. Term c v -> Bool)
runGuard  Any         = const True
runGuard (Atomic   c) = mkGuard isAtomic   c
runGuard (Positive c) = mkGuard isPositive c
runGuard (Negative c) = mkGuard isNegative c
runGuard (gd `And` gd2) = \x -> runGuard gd x && runGuard gd2 x


-- |Smart constructors for guards.
atomic, positive, negative :: (Eq v) => v -> Term c v -> Guard c
atomic   x = Atomic   . fmap (==x)
positive x = Positive . fmap (==x)
negative x = Negative . fmap (==x)


-- * Rules

type RuleId = String

data Rule c v = Rule
  { name       :: ! RuleId
  , guard      :: ! (Guard c)
  , arity      :: ! Int
  , premises   :: ! [Term c v]
  , conclusion :: ! (Term c v)
  }
  deriving (Eq,Ord,Generic)


deriving instance Functor (Rule c)
deriving instance Foldable (Rule c)
deriving instance Traversable (Rule c)
instance (Hashable  c, Hashable  v) => Hashable  (Rule c v)
instance (NFData    c, NFData    v) => NFData    (Rule c v)
instance (Serialize c, Serialize v) => Serialize (Rule c v)


-- |Construct a @Rule@ from a @RuleId@, a list of premises and a conclusion.
mkRule :: RuleId -> [Term c Char] -> Term c Char -> Rule c Int
mkRule n ps c = Rule n Any (length ps) ps' c'
  where
    (c' : ps') = evalState (mapM (mapM label) (c : ps)) (0, IM.empty)

    label x =
      do (i, vm) <- get
         case IM.lookup (ord x) vm of
          Just j -> return j
          _      -> do put (i + 1, IM.insert (ord x) i vm); return i



instance (Show c, ToString v, Show (Term c v)) => Show (Rule c v) where
  showsPrec _ (Rule n g _ ps c) =
    (showString (n++" : ")) .
    (foldr1 (.) (intersperse (showString "→ ") (map shows (ps ++ [c]))))


-- * Substitutions

type VMap c v = IntMap (Term c v)


-- |Apply the given variable map to a given term. Note: the variable
--  map has to contain a term for every variable used in the given
--  term. The resulting term will be variable-free.
subst :: VMap c Void -> Term c Int -> Maybe (Term c Void)
subst s = app where

  app (Con x xs) = Con x <$> mapM app xs
  app (Var i   ) = IM.lookup i s


-- * Systems

data System c = System
  { finite     :: Bool
  , structural :: Bool
  , rules      :: [Rule c Int]

    -- options related to parsing
  , unaryOp    :: Maybe c
  , binaryOp   :: [c]

    -- options related to Agda generation
  , agdaName   :: Maybe String
  , agdaModule :: Maybe String
  }
  deriving (Eq,Ord,Show,Generic)


instance (Hashable  c) => Hashable  (System c)
instance (NFData    c) => NFData    (System c)
instance (Serialize c) => Serialize (System c)


-- |The minimal system. All it is missing is a binary operator.
emptySystem :: System c
emptySystem = System
  { finite     = False
  , structural = False
  , rules      = []

  , unaryOp    = Nothing
  , binaryOp   = []

  , agdaName   = Nothing
  , agdaModule = Nothing
  }

addUnary :: c -> System c -> System c
addUnary op sys = case unaryOp sys of
  Nothing -> sys { unaryOp = Just op }
  Just _  -> error "Cannot parse using more than one unary operator."

addBinary :: c -> System c -> System c
addBinary op sys@System{..} = sys { binaryOp = binaryOp ++ [op] }

addRule :: Rule c Int -> System c -> System c
addRule rule sys@System{..} = sys { rules = rules ++ [rule] }
