module NLIBC where


open import Data.Sum renaming (_⊎_ to Either; inj₁ to Left; inj₂ to Right)


data Atom : Set where
  S  : Atom
  N  : Atom
  NP : Atom

data Kind : Set where
  Solid  : Kind
  Hollow : Kind

data Type : Set where
  El    : Atom -> Type
  UnitR : Kind -> Type -> Type
  ImpR  : Kind -> Type -> Type -> Type
  ImpL  : Kind -> Type -> Type -> Type

data StructI : Set where
  StI  : Type -> StructI
  B    : StructI
  C    : StructI
  UNIT : Kind -> StructI
  PROD : Kind -> StructI -> StructI -> StructI

infixr 5 _⇒_ _⇨_
infixl 5 _⇐_ _⇦_

_⇒_ _⇐_ : Type -> Type -> Type
x ⇒ y = ImpR Solid x y
y ⇐ x = ImpL Solid y x

_⇨_ _⇦_ : Type -> Type -> Type
x ⇨ y = ImpR Hollow x y
y ⇦ x = ImpL Hollow y x

QR : Type -> Type
QR x =  UnitR Hollow x

Q : Type -> Type -> Type -> Type
Q a b c = QR (c ⇦ (a ⇨ b))

T   : StructI
T   = UNIT Hollow


infixr 3 _∙_ _∘_

_∙_ : StructI -> StructI -> StructI
_∙_ = PROD Solid

_∘_ : StructI -> StructI -> StructI
_∘_ = PROD Hollow

data Context : Set where
  HOLE  : Context
  PRODL : Kind -> Context -> StructI -> Context
  PRODR : Kind -> StructI -> Context -> Context

Plug : Context -> StructI -> StructI
Plug HOLE     z = z
Plug (PRODL k x y) z = PROD k (Plug x z) y
Plug (PRODR k x y) z = PROD k x (Plug y z)

data Context1 : Set where
  HOLE : Context1
  _<∙_ : Context1 -> StructI  -> Context1
  _∙>_ : StructI  -> Context1 -> Context1

Trace : Context1 -> StructI
Trace HOLE     = T
Trace (x ∙> y) = (B ∙ x) ∙ Trace y
Trace (x <∙ y) = (C ∙ Trace x) ∙ y

Plug1 : Context1 -> StructI -> StructI
Plug1 HOLE     z = z
Plug1 (x <∙ y) z = (Plug1 x z) ∙ y
Plug1 (x ∙> y) z = x ∙ (Plug1 y z)


data Pos : Type -> Set where
  Pos_N      :            Pos (El N)
  Pos_NP     :            Pos (El NP)
  Pos_UnitR  : ∀ {k a} -> Pos (UnitR k a)

data Neg : Type -> Set where
  Neg_S      :              Neg (El S)
  Neg_ImpR   : ∀ {k a b} -> Neg (ImpR k a b)
  Neg_ImpL   : ∀ {k a b} -> Neg (ImpL k b a)

pol : (a : Type) -> Either (Pos a) (Neg a)
pol (El S)       = Right Neg_S
pol (El N)       = Left  Pos_N
pol (El NP)      = Left  Pos_NP
pol (UnitR _ _)  = Left  Pos_UnitR
pol (ImpR _ _ _) = Right Neg_ImpR
pol (ImpL _ _ _) = Right Neg_ImpL


module SC where

  infix 1 _⊢_

  data Sequent : Set where
    _⊢_ : StructI -> Type -> Sequent

  data Prf : Sequent -> Set where

    Ax     : ∀ {a}
          -> Prf (StI a ⊢ a)

    ImpRL  : ∀ {k x a b c} (σ : Context)
          -> Prf (x ⊢ a)
          -> Prf (Plug σ (StI b) ⊢ c)
          -> Prf (Plug σ (PROD k x (StI (ImpR k a b))) ⊢ c)

    ImpRR  : ∀ {k x a b}
          -> Prf (PROD k (StI a) x ⊢ b)
          -> Prf (x ⊢ ImpR k a b)

    ImpLL  : ∀ {k x a b c} (σ : Context)
          -> Prf (x ⊢ a)
          -> Prf (Plug σ (StI b) ⊢ c)
          -> Prf (Plug σ (PROD k (StI (ImpL k b a)) x) ⊢ c)

    ImpLR  : ∀ {k x a b}
          -> Prf (PROD k x (StI a) ⊢ b)
          -> Prf (x ⊢ ImpL k b a)

    UnitRE : ∀ {k a b} (σ : Context)
          -> Prf (Plug σ (PROD k (StI a) (UNIT k)) ⊢ b)
          -> Prf (Plug σ (StI (UnitR k a)) ⊢ b)

    UnitRI : ∀ {k x b} (σ : Context)
          -> Prf (Plug σ x ⊢ b)
          -> Prf (Plug σ (PROD k x (UNIT k)) ⊢ b)

    UpB    : ∀ {x y z b} (σ : Context)
          -> Prf (Plug σ (x ∙ (y ∘ z)) ⊢ b)
          -> Prf (Plug σ (y ∘ ((B ∙ x) ∙ z)) ⊢ b)

    DnB    : ∀ {x y z b} (σ : Context)
          -> Prf (Plug σ (y ∘ ((B ∙ x) ∙ z)) ⊢ b)
          -> Prf (Plug σ (x ∙ (y ∘ z)) ⊢ b)

    UpC    : ∀ {x y z b} (σ : Context)
          -> Prf (Plug σ ((x ∘ y) ∙ z) ⊢ b)
          -> Prf (Plug σ (x ∘ ((C ∙ y) ∙ z)) ⊢ b)

    DnC    : ∀ {x y z b} (σ : Context)
          -> Prf (Plug σ (x ∘ ((C ∙ y) ∙ z)) ⊢ b)
          -> Prf (Plug σ ((x ∘ y) ∙ z) ⊢ b)


module DC where

  infix  1 _⊢_ _⊢>_ _<⊢_

  data StructO : Set where
    StO  : Type -> StructO
    IMPR : Kind -> StructI -> StructO -> StructO
    IMPL : Kind -> StructO -> StructI -> StructO

  data Sequent : Set where
    _⊢_  : StructI -> StructO -> Sequent
    _<⊢_ : Type    -> StructO -> Sequent
    _⊢>_ : StructI -> Type    -> Sequent

  data Prf : Sequent -> Set where

    AxR    : ∀ {b}         -> Pos b -> Prf (StI b ⊢> b)
    AxL    : ∀ {a}         -> Neg a -> Prf (a <⊢ StO a)
    UnfR   : ∀ {x b}       -> Neg b -> Prf (x ⊢ StO b) -> Prf (x ⊢> b)
    UnfL   : ∀ {a y}       -> Pos a -> Prf (StI a ⊢ y) -> Prf (a <⊢ y)
    FocR   : ∀ {x b}       -> Pos b -> Prf (x ⊢> b) -> Prf (x ⊢ StO b)
    FocL   : ∀ {a y}       -> Neg a -> Prf (a <⊢ y) -> Prf (StI a ⊢ y)

    ImpRL  : ∀ {k x y a b} -> Prf (x ⊢> a) -> Prf (b <⊢ y) -> Prf (ImpR k a b <⊢ IMPR k x y)
    ImpRR  : ∀ {k x a b}   -> Prf (x ⊢ IMPR k (StI a) (StO b)) -> Prf (x ⊢ StO (ImpR k a b))
    ImpLL  : ∀ {k x y a b} -> Prf (x ⊢> a) -> Prf (b <⊢ y) -> Prf (ImpL k b a <⊢ IMPL k y x)
    ImpLR  : ∀ {k x a b}   -> Prf (x ⊢ IMPL k (StO b) (StI a)) -> Prf (x ⊢ StO (ImpL k b a))
    Res11  : ∀ {k x y z}   -> Prf (y ⊢ IMPR k x z) -> Prf (PROD k x y ⊢ z)
    Res12  : ∀ {k x y z}   -> Prf (PROD k x y ⊢ z) -> Prf (y ⊢ IMPR k x z)
    Res13  : ∀ {k x y z}   -> Prf (x ⊢ IMPL k z y) -> Prf (PROD k x y ⊢ z)
    Res14  : ∀ {k x y z}   -> Prf (PROD k x y ⊢ z) -> Prf (x ⊢ IMPL k z y)

    UnitRL : ∀ {k a y}     -> Prf (PROD k (StI a) (UNIT k) ⊢ y) -> Prf (StI (UnitR k a) ⊢ y)
    UnitRR : ∀ {k x b}     -> Prf (x ⊢> b) -> Prf (PROD k x (UNIT k) ⊢> UnitR k b)
    UnitRI : ∀ {k x y}     -> Prf (x ⊢ y) -> Prf (PROD k x (UNIT k) ⊢ y)

    UpB    : ∀ {x y z w}   -> Prf (x ∙ (y ∘ z) ⊢ w) -> Prf (y ∘ ((B ∙ x) ∙ z) ⊢ w)
    DnB    : ∀ {x y z w}   -> Prf (y ∘ ((B ∙ x) ∙ z) ⊢ w) -> Prf (x ∙ (y ∘ z) ⊢ w)
    UpC    : ∀ {x y z w}   -> Prf ((x ∘ y) ∙ z ⊢ w) -> Prf (x ∘ ((C ∙ y) ∙ z) ⊢ w)
    DnC    : ∀ {x y z w}   -> Prf (x ∘ ((C ∙ y) ∙ z) ⊢ w) -> Prf ((x ∘ y) ∙ z ⊢ w)


  qrL : ∀ (x : Context1) {y b c}
     -> Prf (Trace x ⊢> b)
     -> Prf (c <⊢ y)
     -> Prf (Plug1 x (StI (QR (c ⇦ b))) ⊢ y)
  qrL x f g = init x (move x (Res13 (FocL Neg_ImpL (ImpLL f g))))
    where
      init : ∀ (x : Context1) {y a}
          -> Prf (Plug1 x (StI a ∘ T) ⊢ y)
          -> Prf (Plug1 x (StI (QR a)) ⊢ y)
      init HOLE     f = UnitRL f
      init (x <∙ y) f = Res13 (init x (Res14 f))
      init (x ∙> y) f = Res11 (init y (Res12 f))

      move : ∀ (x : Context1) {y z}
          -> Prf (y ∘ Trace x ⊢ z)
          -> Prf (Plug1 x (y ∘ T) ⊢ z)
      move HOLE     f = f
      move (x <∙ y) f = Res13 (move x (Res14 (DnC f)))
      move (x ∙> y) f = Res11 (move y (Res12 (DnB f)))

  qrR : ∀ (x : Context1) {a b}
     -> Prf (Plug1 x (StI a) ⊢ StO b)
     -> Prf (Trace x ⊢ StO (a ⇨ b))
  qrR x f = ImpRR (Res12 (move x f))
    where
      move : ∀ (x : Context1) {y z}
          -> Prf (Plug1 x y ⊢ z)
          -> Prf (y ∘ Trace x ⊢ z)
      move HOLE     f = UnitRI f
      move (x <∙ y) f = UpC (Res13 (move x (Res14 f)))
      move (x ∙> y) f = UpB (Res11 (move y (Res12 f)))


-- -}
-- -}
-- -}
-- -}
-- -}
