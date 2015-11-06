module NLIBC where


open import Data.Sum renaming (_⊎_ to Either; inj₁ to Left; inj₂ to Right)


infix  2 _⊢_ _⊢[_] [_]⊢_
infixr 5 _∙_ _∘_


data Atom : Set where
  S   : Atom
  N   : Atom
  NP  : Atom
  PP  : Atom
  INF : Atom

data Kind : Set where
  Solid    : Kind
  Hollow   : Kind
  Infixate : Kind
  Extract  : Kind

data Type : Set where
  El    : Atom -> Type
  Dia   : Kind -> Type -> Type
  Box   : Kind -> Type -> Type
  UnitR : Kind -> Type -> Type
  ImpR  : Kind -> Type -> Type -> Type
  ImpL  : Kind -> Type -> Type -> Type

data StructI : Set where
  ·_·  : Type -> StructI
  B    : StructI
  C    : StructI
  DIA  : Kind -> StructI -> StructI
  UNIT : Kind -> StructI
  PROD : Kind -> StructI -> StructI -> StructI

data StructO : Set where
  ·_·  : Type -> StructO
  BOX  : Kind -> StructO -> StructO
  IMPR : Kind -> StructI -> StructO -> StructO
  IMPL : Kind -> StructO -> StructI -> StructO

data Sequent : Set where
  _⊢_   : StructI -> StructO -> Sequent
  [_]⊢_ : Type    -> StructO -> Sequent
  _⊢[_] : StructI -> Type    -> Sequent


T   = UNIT  Hollow
QR  = UnitR Hollow
Ifx = \ A -> Dia Infixate (Box Infixate A)
IFX = DIA   Infixate
Ext = \ A -> Dia Extract (Box Extract A)
EXT = DIA   Extract
_∙_ = PROD  Solid
_⇒_ = ImpR  Solid
_⇐_ = ImpL  Solid
_∘_ = PROD  Hollow
_⇨_ = ImpR  Hollow
_⇦_ = ImpL  Hollow


data Pos : Type -> Set where
  Pos_N      : Pos (El N)
  Pos_NP     : Pos (El NP)
  Pos_PP     : Pos (El PP)
  Pos_INF    : Pos (El INF)
  Pos_Dia    : ∀ {k a} -> Pos (Dia k a)
  Pos_UnitR  : ∀ {k a} -> Pos (UnitR k a)

data Neg : Type -> Set where
  Neg_S      : Neg (El S)
  Neg_Box    : ∀ {k a} -> Neg (Box k a)
  Neg_ImpR   : ∀ {k a b} -> Neg (ImpR k a b)
  Neg_ImpL   : ∀ {k a b} -> Neg (ImpL k b a)

pol : (a : Type) -> Either (Pos a) (Neg a)
pol (El S)       = Right Neg_S
pol (El N)       = Left  Pos_N
pol (El NP)      = Left  Pos_NP
pol (El PP)      = Left  Pos_PP
pol (El INF)     = Left  Pos_INF
pol (Dia _ _)    = Left  Pos_Dia
pol (Box _ _)    = Right Neg_Box
pol (UnitR _ _)  = Left  Pos_UnitR
pol (ImpR _ _ _) = Right Neg_ImpR
pol (ImpL _ _ _) = Right Neg_ImpL


infixr 5 _<∙_ _∙>_

data Context : Set where
  HOLE : Context
  _<∙_ : Context -> StructI -> Context
  _∙>_ : StructI -> Context -> Context

Plug : Context -> StructI -> StructI
Plug HOLE     z = z
Plug (x <∙ y) z = (Plug x z) ∙ y
Plug (x ∙> y) z = x ∙ (Plug y z)

Trace : Context -> StructI
Trace HOLE     = T
Trace (x ∙> y) = (B ∙ x) ∙ (Trace y)
Trace (x <∙ y) = (C ∙ (Trace x)) ∙ y


infix 1 Prf_

data Prf_ : Sequent -> Set where
  AxR    : ∀ {b}           -> Pos b -> Prf · b · ⊢[ b ]
  AxL    : ∀ {a}           -> Neg a -> Prf [ a ]⊢ · a ·
  UnfR   : ∀ {x b}         -> Neg b -> Prf x ⊢ · b · -> Prf x ⊢[ b ]
  UnfL   : ∀ {a y}         -> Pos a -> Prf · a · ⊢ y -> Prf [ a ]⊢ y
  FocR   : ∀ {x b}         -> Pos b -> Prf x ⊢[ b ] -> Prf x ⊢ · b ·
  FocL   : ∀ {a y}         -> Neg a -> Prf [ a ]⊢ y -> Prf · a · ⊢ y

  ImpRL  : ∀ {k x y a b}   -> Prf x ⊢[ a ] -> Prf [ b ]⊢ y -> Prf [ ImpR k a b ]⊢ IMPR k x y
  ImpRR  : ∀ {k x a b}     -> Prf x ⊢ IMPR k · a · · b · -> Prf x ⊢ · ImpR k a b ·
  ImpLL  : ∀ {k x y a b}   -> Prf x ⊢[ a ] -> Prf [ b ]⊢ y -> Prf [ ImpL k b a ]⊢ IMPL k y x
  ImpLR  : ∀ {k x a b}     -> Prf x ⊢ IMPL k · b · · a · -> Prf x ⊢ · ImpL k b a ·
  Res11  : ∀ {k x y z}     -> Prf y ⊢ IMPR k x z -> Prf PROD k x y ⊢ z
  Res12  : ∀ {k x y z}     -> Prf PROD k x y ⊢ z -> Prf y ⊢ IMPR k x z
  Res13  : ∀ {k x y z}     -> Prf x ⊢ IMPL k z y -> Prf PROD k x y ⊢ z
  Res14  : ∀ {k x y z}     -> Prf PROD k x y ⊢ z -> Prf x ⊢ IMPL k z y

  DiaL   : ∀ {k a y}       -> Prf DIA k · a · ⊢ y -> Prf · Dia k a · ⊢ y
  DiaR   : ∀ {k x b}       -> Prf x ⊢[ b ] -> Prf DIA k x ⊢[ Dia k b ]
  BoxL   : ∀ {k a y}       -> Prf [ a ]⊢ y -> Prf [ Box k a ]⊢ BOX k y
  BoxR   : ∀ {k x b}       -> Prf x ⊢ BOX k · b · -> Prf x ⊢ · Box k b ·
  Res21  : ∀ {k x y}       -> Prf x ⊢ BOX k y -> Prf DIA k x ⊢ y
  Res22  : ∀ {k x y}       -> Prf DIA k x ⊢ y -> Prf x ⊢ BOX k y

  IfxRR  : ∀ {x y z w}     -> Prf ((x ∙ y) ∙ IFX z ⊢ w) -> Prf (x ∙ (y ∙ IFX z) ⊢ w)
  IfxLR  : ∀ {x y z w}     -> Prf ((x ∙ y) ∙ IFX z ⊢ w) -> Prf ((x ∙ IFX z) ∙ y ⊢ w)
  IfxLL  : ∀ {x y z w}     -> Prf (IFX z ∙ (y ∙ x) ⊢ w) -> Prf ((IFX z ∙ y) ∙ x ⊢ w)
  IfxRL  : ∀ {x y z w}     -> Prf (IFX z ∙ (y ∙ x) ⊢ w) -> Prf (y ∙ (IFX z ∙ x) ⊢ w)

  ExtRR  : ∀ {x y z w}     -> Prf (x ∙ (y ∙ EXT z) ⊢ w) -> Prf ((x ∙ y) ∙ EXT z ⊢ w)
  ExtLR  : ∀ {x y z w}     -> Prf ((x ∙ EXT z) ∙ y ⊢ w) -> Prf ((x ∙ y) ∙ EXT z ⊢ w)
  ExtLL  : ∀ {x y z w}     -> Prf ((EXT z ∙ y) ∙ x ⊢ w) -> Prf (EXT z ∙ (y ∙ x) ⊢ w)
  ExtRL  : ∀ {x y z w}     -> Prf (y ∙ (EXT z ∙ x) ⊢ w) -> Prf (EXT z ∙ (y ∙ x) ⊢ w)

  UnitRL : ∀ {k y a}       -> Prf PROD k · a · (UNIT k) ⊢ y -> Prf · UnitR k a · ⊢ y
  UnitRR : ∀ {k x b}       -> Prf x ⊢[ b ] -> Prf PROD k x (UNIT k) ⊢[ UnitR k b ]
  UnitRI : ∀ {k x y}       -> Prf x ⊢ y -> Prf PROD k x (UNIT k) ⊢ y

  UpB    : ∀ {x z a w}     -> Prf x ∙ (· a · ∘ z) ⊢ w -> Prf · a · ∘ ((B ∙ x) ∙ z) ⊢ w
  UpC    : ∀ {y z a w}     -> Prf (· a · ∘ y) ∙ z ⊢ w -> Prf · a · ∘ ((C ∙ y) ∙ z) ⊢ w
  DnB    : ∀ {x z a b c w} -> Prf · c ⇦ (a ⇨ b) · ∘ ((B ∙ x) ∙ z) ⊢ w -> Prf x ∙ (· c ⇦ (a ⇨ b) · ∘ z) ⊢ w
  DnC    : ∀ {y z a b c w} -> Prf · c ⇦ (a ⇨ b) · ∘ ((C ∙ y) ∙ z) ⊢ w -> Prf (· c ⇦ (a ⇨ b) · ∘ y) ∙ z ⊢ w


Up' : ∀ (x : Context) {y a b c}
     -> Prf Trace x ⊢[ a ⇨ b ]
     -> Prf [ c ]⊢ y
     -> Prf Plug x (· QR (c ⇦ (a ⇨ b)) ·) ⊢ y
Up' x f g = init x (move x (Res13 (FocL Neg_ImpL (ImpLL f g))))
  where
    init : ∀ (x : Context) {a y}
         -> Prf Plug x (· a · ∘ T) ⊢ y
         -> Prf Plug x (· QR a ·) ⊢ y
    init HOLE     f = UnitRL f
    init (x <∙ y) f = Res13 (init x (Res14 f))
    init (x ∙> y) f = Res11 (init y (Res12 f))

    move : ∀ (x : Context) {z a b c}
         -> Prf · c ⇦ (a ⇨ b) ·  ∘ Trace x ⊢ z
         -> Prf Plug x (· c ⇦ (a ⇨ b) · ∘ T) ⊢ z
    move HOLE     f = f
    move (x <∙ y) f = Res13 (move x (Res14 (DnC f)))
    move (x ∙> y) f = Res11 (move y (Res12 (DnB f)))


Dn' : ∀ (x : Context) {a b}
     -> Prf Plug x · a · ⊢ · b ·
     -> Prf Trace x ⊢ · a ⇨ b ·
Dn' x f = ImpRR (Res12 (move x f))
  where
    move : ∀ (x : Context) {a z}
         -> Prf Plug x · a · ⊢ z
         -> Prf · a · ∘ Trace x ⊢ z
    move HOLE     f = UnitRI f
    move (x <∙ y) f = UpC (Res13 (move x (Res14 f)))
    move (x ∙> y) f = UpB (Res11 (move y (Res12 f)))


BOOK   = El N
THE    = El NP ⇐ El N
AUTHOR = El N
OF     = (El N ⇒ El N) ⇐ El N
WHICH  = QR(((El N ⇒ El N) ⇐ (El S ⇐ Ext (El NP))) ⇦ (El N ⇨ El NP))
JOHN   = El NP
LIKES  = (El NP ⇒ El S) ⇐ El NP


prf1 : Prf · THE · ∙ · AUTHOR · ∙ · OF · ∙ · El N · ⊢ · El NP ·
prf1 = Res11 (Res11 (Res13 (FocL Neg_ImpL (ImpLL (AxR Pos_N) (ImpRL (AxR Pos_N)
       (UnfL Pos_N (Res12 (Res13 (FocL Neg_ImpL (ImpLL (AxR Pos_N) (UnfL Pos_NP
       (FocR Pos_NP (AxR Pos_NP)))))))))))))

prf2 : Prf · JOHN · ∙ · LIKES · ⊢[ El S ⇐ Ext (El NP) ]
prf2 = UnfR Neg_ImpL (ImpLR (Res14 (Res11 (DiaL (Res12 (ExtRR (Res11 (Res11
       (Res21 (FocL Neg_Box (BoxL (UnfL Pos_NP (Res12 (Res13 (FocL Neg_ImpL
       (ImpLL (AxR Pos_NP) (ImpRL (AxR Pos_NP) (AxL Neg_S))))))))))))))))))

prf3 : Prf · BOOK · ∙ (· THE · ∙ · AUTHOR · ∙ · OF · ∙ · WHICH ·) ∙ (· JOHN · ∙ · LIKES ·) ⊢ · El N ·
prf3 = Res11 (Res13 (Up' (_ ∙> (_ ∙> (_ ∙> HOLE))) (UnfR Neg_ImpR
       (Dn' (_ ∙> (_ ∙> (_ ∙> HOLE))) prf1)) (ImpLL prf2 (ImpRL (AxR Pos_N)
       (UnfL Pos_N (FocR Pos_N (AxR Pos_N)))))))
