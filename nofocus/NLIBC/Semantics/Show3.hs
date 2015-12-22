{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
module NLIBC.Semantics.Show3 where


data E
data T

data Z   = Z
data S n = S n

class    Nat n              where nat :: n -> Int
instance Nat Z              where nat _ = 0
instance Nat n => Nat (S n) where nat _ = 1 + nat (undefined::n)

-- Maximum of two numerals
type family   Max  n1     n2    :: *
type instance Max  Z      n2    = n2
type instance Max (S n1)  Z     = S n1
type instance Max (S n1) (S n2) = S (Max n1 n2)


class Sym repr where
  john :: repr Z E
  mary :: repr Z E
  see  :: repr Z (E -> E -> T)
  app  :: repr n1 (a -> b) -> repr n2 a -> repr (Max n1 n2) b

  var    :: Nat n => n -> repr (S n) E
  forall :: Nat n => repr (S n) T -> repr n T
  exists :: Nat n => repr (S n) T -> repr n T
