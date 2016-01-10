module NLIBC where


open import Level using (_⊔_)


data Polarity : Set where + - : Polarity

record Polarised (A : Set) : Set where
  field
    Pol : A → Polarity
open Polarised {{...}}

record Translate {t1 t2} (T1 : Set t1) (T2 : Set t2) : Set (t1 ⊔ t2) where
  field
    _* : T1 → T2
open Translate {{...}}


module Syn (Atom : Set) (PolarisedAtom : Polarised Atom) where


  open import Data.Product                               using (∃; _,_)
  open import Function                                   using (flip)
  open import Function.Equality                          using (_⟨$⟩_)
  open import Function.Equivalence                  as F using (_⇔_; equivalence)
  open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; inspect)
  open F.Equivalence using (from; to)


  -- ** Kinds, Types, Structures and Sequents

  data Kind : Set where
    Sol : Kind
    Hol : Kind
    Ifx : Kind
    Ext : Kind

  data Type : Set where
    El    : Atom → Type
    Dia   : Kind → Type → Type
    Box   : Kind → Type → Type
    _&_   : Type → Type → Type
    UnitR : Kind → Type → Type
    ImpR  : Kind → Type → Type → Type
    ImpL  : Kind → Type → Type → Type

  data Struct : Polarity → Set where
    ·_·  : ∀ {p} → Type → Struct p
    B    : Struct +
    C    : Struct +
    DIA  : Kind → Struct + → Struct +
    UNIT : Kind → Struct +
    PROD : Kind → Struct + → Struct + → Struct +
    BOX  : Kind → Struct - → Struct -
    IMPR : Kind → Struct + → Struct - → Struct -
    IMPL : Kind → Struct - → Struct + → Struct -

  data Sequent : Set where
    _⊢_   : Struct + → Struct - → Sequent
    [_]⊢_ : Type     → Struct - → Sequent
    _⊢[_] : Struct + → Type     → Sequent


  -- ** Polarity

  instance
    PolarisedType : Polarised Type
    PolarisedType = record { Pol = Pol' }
      where
        Pol' : Type → Polarity
        Pol' (El    a)     = Pol(a)
        Pol' (Dia   _ _)   = +
        Pol' (Box   _ _)   = -
        Pol' (a & b)       = +
        Pol' (UnitR _ _)   = +
        Pol' (ImpR  _ _ _) = -
        Pol' (ImpL  _ _ _) = -



  -- ** Type and Structure aliases

  -- *** Base Types
  infixr 3 _∙_; pattern _∙_ x y = PROD  Sol x y
  infixr 7 _⇐_; pattern _⇐_ b a = ImpL  Sol b a
  infixl 7 _⇒_; pattern _⇒_ a b = ImpR  Sol a b

  -- *** Quantifier Raising
  pattern I    = UNIT  Hol
  pattern Q a  = UnitR Hol a

  infixr 3 _∘_; pattern _∘_ x y = PROD  Hol x y
  infixr 7 _⇨_; pattern _⇨_ a b = ImpR  Hol a b
  infixl 7 _⇦_; pattern _⇦_ b a = ImpL  Hol b a

  -- *** Scope Islands and Reset
  infixr 9 ◇_; pattern ◇_ a = Dia Res a
  infixr 9 □_; pattern □_ a = Box Res a
  infixr 9 ◆_; pattern ◆_ x = DIA Res x
  infixr 9 ■_; pattern ■_ x = BOX Res x

  -- *** Infixation
  infixr 9 ◇↑_; pattern ◇↑_ a   = Dia Ifx a
  infixr 9 □↑_; pattern □↑_ a   = Box Ifx a
  infixr 9 ◆↑_; pattern ◆↑_ x   = DIA Ifx x
  infixr 9 ■↑_; pattern ■↑_ x   = BOX Ifx x
  infix  7 _↿_; pattern _↿_ a b = ◇↑ □↑ (a ⇒ b)
  infix  7 _↾_; pattern _↾_ b a = ◇↑ □↑ (b ⇐ a)

  -- *** Extraction
  infixr 9 ◇↓_; pattern ◇↓_ a   = Dia Ext a
  infixr 9 □↓_; pattern □↓_ a   = Box Ext a
  infixr 9 ◆↓_; pattern ◆↓_ x   = DIA Ext x
  infixr 9 ■↓_; pattern ■↓_ x   = BOX Ext x
  infix  7 _⇃_; pattern _⇃_ a b = (◇↓ □↓ a) ⇒ b
  infix  7 _⇂_; pattern _⇂_ b a = b ⇐ (◇↓ □↓ a)



  -- ** Contexts and Plugging functions

  record Pluggable (F I : Polarity → Set) (O : Set) : Set where
    field
      _[_] : ∀ {p} → F p → I p → O
  open Pluggable {{...}}

  -- *** Contexts for Structures
  data StructContext (p : Polarity) : Polarity → Set where
    HOLE  : StructContext p p
    DIA1  : Kind → StructContext p + → StructContext p +
    PROD1 : Kind → StructContext p + → Struct          + → StructContext p +
    PROD2 : Kind → Struct          + → StructContext p + → StructContext p +
    BOX1  : Kind → StructContext p - → StructContext p -
    IMPR1 : Kind → StructContext p + → Struct          - → StructContext p -
    IMPR2 : Kind → Struct          + → StructContext p - → StructContext p -
    IMPL1 : Kind → StructContext p - → Struct          + → StructContext p -
    IMPL2 : Kind → Struct          - → StructContext p + → StructContext p -

  instance
    Pluggable-Struct : ∀ {p} → Pluggable (flip StructContext p) Struct (Struct p)
    Pluggable-Struct = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p1 p2} → StructContext p1 p2 → Struct p1 → Struct p2
        (HOLE       ) [ z ]′ = z
        (DIA1  k x  ) [ z ]′ = DIA  k   (x [ z ]′)
        (PROD1 k x y) [ z ]′ = PROD k   (x [ z ]′) y
        (PROD2 k x y) [ z ]′ = PROD k x (y [ z ]′)
        (BOX1  k x  ) [ z ]′ = BOX  k   (x [ z ]′)
        (IMPR1 k x y) [ z ]′ = IMPR k   (x [ z ]′) y
        (IMPR2 k x y) [ z ]′ = IMPR k x (y [ z ]′)
        (IMPL1 k x y) [ z ]′ = IMPL k   (x [ z ]′) y
        (IMPL2 k x y) [ z ]′ = IMPL k x (y [ z ]′)

  -- *** Contexts for Sequents
  data SequentContext (p : Polarity) : Set where
    _<⊢_ : StructContext p + → Struct          - → SequentContext p
    _⊢>_ : Struct          + → StructContext p - → SequentContext p

  instance
    Pluggable-Sequent : Pluggable SequentContext Struct Sequent
    Pluggable-Sequent = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p} → SequentContext p → Struct p → Sequent
        (x <⊢ y) [ z ]′ = x [ z ] ⊢ y
        (x ⊢> y) [ z ]′ = x ⊢ y [ z ]


  -- *** Contexts for Display Sequents
  data DisplayContext : Polarity → Set where
    <⊢_ : Struct - → DisplayContext +
    _⊢> : Struct + → DisplayContext -

  instance
    Pluggable-Display : Pluggable DisplayContext Struct Sequent
    Pluggable-Display = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p} → DisplayContext p → Struct p → Sequent
        (<⊢ y) [ x ]′ = x ⊢ y
        (x ⊢>) [ y ]′ = x ⊢ y


  -- ** Inference Rules

  infix 1 NL_
  infix 2 _⊢_

  data NL_ : Sequent -> Set where
    axElR  : ∀ {b}         → Pol(b) ≡ + → NL · El b · ⊢[ El b ]
    axElL  : ∀ {a}         → Pol(a) ≡ - → NL [ El a ]⊢ · El a ·
    unfR   : ∀ {x b}       → Pol(b) ≡ - → NL x ⊢ · b · → NL x ⊢[ b ]
    unfL   : ∀ {a y}       → Pol(a) ≡ + → NL · a · ⊢ y → NL [ a ]⊢ y
    focR   : ∀ {x b}       → Pol(b) ≡ + → NL x ⊢[ b ] → NL x ⊢ · b ·
    focL   : ∀ {a y}       → Pol(a) ≡ - → NL [ a ]⊢ y → NL · a · ⊢ y

    impRL  : ∀ {k x y a b} → NL x ⊢[ a ] → NL [ b ]⊢ y → NL [ ImpR k a b ]⊢ IMPR k x y
    impRR  : ∀ {k x a b}   → NL x ⊢ IMPR k · a · · b · → NL x ⊢ · ImpR k a b ·
    impLL  : ∀ {k x y a b} → NL x ⊢[ a ] → NL [ b ]⊢ y → NL [ ImpL k b a ]⊢ IMPL k y x
    impLR  : ∀ {k x a b}   → NL x ⊢ IMPL k · b · · a · → NL x ⊢ · ImpL k b a ·
    resRP  : ∀ {k x y z}   → NL y ⊢ IMPR k x z → NL PROD k x y ⊢ z
    resPR  : ∀ {k x y z}   → NL PROD k x y ⊢ z → NL y ⊢ IMPR k x z
    resLP  : ∀ {k x y z}   → NL x ⊢ IMPL k z y → NL PROD k x y ⊢ z
    resPL  : ∀ {k x y z}   → NL PROD k x y ⊢ z → NL x ⊢ IMPL k z y

    withL1 : ∀ {a1 a2 y}   → NL [ a1 ]⊢ y  → NL · a1 & a2 · ⊢ y
    withL2 : ∀ {a1 a2 y}   → NL [ a2 ]⊢ y  → NL · a1 & a2 · ⊢ y
    withR  : ∀ {b1 b2 x}   → NL x ⊢ · b1 · → NL x ⊢ · b2 · → NL x ⊢[ b1 & b2 ]

    unitRL : ∀ {k y a}     → NL PROD k · a · (UNIT k) ⊢ y → NL · UnitR k a · ⊢ y
    unitRR : ∀ {k x b}     → NL x ⊢[ b ] → NL PROD k x (UNIT k) ⊢[ UnitR k b ]
    unitRI : ∀ {k x y}     → NL x ⊢ y → NL PROD k x (UNIT k) ⊢ y

    diaL   : ∀ {k a y}     → NL DIA k · a · ⊢ y → NL · Dia k a · ⊢ y
    diaR   : ∀ {k x b}     → NL x ⊢[ b ] → NL DIA k x ⊢[ Dia k b ]
    boxL   : ∀ {k a y}     → NL [ a ]⊢ y → NL [ Box k a ]⊢ BOX k y
    boxR   : ∀ {k x b}     → NL x ⊢ BOX k · b · → NL x ⊢ · Box k b ·
    resBD  : ∀ {k x y}     → NL x ⊢ BOX k y → NL DIA k x ⊢ y
    resDB  : ∀ {k x y}     → NL DIA k x ⊢ y → NL x ⊢ BOX k y

    upB    : ∀ {x y z w}   → NL x ∙ (y ∘ z) ⊢ w       → NL y ∘ ((B ∙ x) ∙ z) ⊢ w
    upC    : ∀ {x y z w}   → NL (x ∘ y) ∙ z ⊢ w       → NL x ∘ ((C ∙ y) ∙ z) ⊢ w
    dnB    : ∀ {x y z w}   → NL y ∘ ((B ∙ x) ∙ z) ⊢ w → NL x ∙ (y ∘ z) ⊢ w
    dnC    : ∀ {x y z w}   → NL x ∘ ((C ∙ y) ∙ z) ⊢ w → NL (x ∘ y) ∙ z ⊢ w

    ifxRR  : ∀ {x y z w}   → NL ((x ∙ y) ∙ ◆↑ z ⊢ w) → NL (x ∙ (y ∙ ◆↑ z) ⊢ w)
    ifxLR  : ∀ {x y z w}   → NL ((x ∙ y) ∙ ◆↑ z ⊢ w) → NL ((x ∙ ◆↑ z) ∙ y ⊢ w)
    ifxLL  : ∀ {x y z w}   → NL (◆↑ z ∙ (y ∙ x) ⊢ w) → NL ((◆↑ z ∙ y) ∙ x ⊢ w)
    ifxRL  : ∀ {x y z w}   → NL (◆↑ z ∙ (y ∙ x) ⊢ w) → NL (y ∙ (◆↑ z ∙ x) ⊢ w)

    extRR  : ∀ {x y z w}   → NL (x ∙ (y ∙ ◆↓ z) ⊢ w) → NL ((x ∙ y) ∙ ◆↓ z ⊢ w)
    extLR  : ∀ {x y z w}   → NL ((x ∙ ◆↓ z) ∙ y ⊢ w) → NL ((x ∙ y) ∙ ◆↓ z ⊢ w)
    extLL  : ∀ {x y z w}   → NL ((◆↓ z ∙ y) ∙ x ⊢ w) → NL (◆↓ z ∙ (y ∙ x) ⊢ w)
    extRL  : ∀ {x y z w}   → NL (y ∙ (◆↓ z ∙ x) ⊢ w) → NL (◆↓ z ∙ (y ∙ x) ⊢ w)

  resRL : ∀ {k x y z} → NL y ⊢ IMPR k x z → NL x ⊢ IMPL k z y
  resRL f = resPL (resRP f)
  resLR : ∀ {k x y z} → NL x ⊢ IMPL k z y → NL y ⊢ IMPR k x z
  resLR f = resPR (resLP f)



  -- ** Display Property

  -- `DP` is a type-level function, which takes a sequent context (a
  -- sequent with exactly one hole) and computes the sequent in which
  -- the formula in that hole can be displayed (i.e. brought to the
  -- top-level). This is implemented with two potentially mutually
  -- recursive, which manipulate the antecedent and succedent.
  mutual
    DP : ∀ {p} (s : SequentContext p) → DisplayContext p
    DP (x <⊢ y) = DPL x y
    DP (x ⊢> y) = DPR x y

    DPL : ∀ {p} (x : StructContext p +) (y : Struct -) → DisplayContext p
    DPL (HOLE       ) z = <⊢ z
    DPL (DIA1  k x  ) z = DPL x (BOX  k z)
    DPL (PROD1 k x y) z = DPL x (IMPL k z y)
    DPL (PROD2 k x y) z = DPL y (IMPR k x z)

    DPR : ∀ {p} (x : Struct +) (y : StructContext p -) → DisplayContext p
    DPR x (HOLE       ) = x ⊢>
    DPR x (BOX1  k y  ) = DPR   (DIA  k x)   y
    DPR x (IMPR1 k y z) = DPL y (IMPL k z x)
    DPR x (IMPR2 k y z) = DPR   (PROD k y x) z
    DPR x (IMPL1 k z y) = DPR   (PROD k x y) z
    DPR x (IMPL2 k z y) = DPL y (IMPR k x z)

  -- `dp` is a term-level function, which takes a sequent context `s` (as
  -- above), a structure `w`, and a proof for the sequent `s [ w ]`.
  -- It then computes an isomorphism between proofs of `s [ w ]` and
  -- proofs of `DP s [ w ]` where, in the second proof, the formula
  -- `w` is guaranteed to be displayed.
  mutual
    dp : ∀ {p} (s : SequentContext p) (w : Struct p) → (NL s [ w ]) ⇔ (NL DP s [ w ])
    dp (x <⊢ y) w = dpL x y w
    dp (x ⊢> y) w = dpR x y w

    dpL : ∀ {p} (x : StructContext p +) (y : Struct -) (w : Struct p)
        → (NL x [ w ] ⊢ y) ⇔ (NL DPL x y [ w ])
    dpL  HOLE         z w = F.id
    dpL (DIA1  k x)   z w = dpL x (BOX  k z)   w F.∘ F.equivalence resDB resBD
    dpL (PROD1 k x y) z w = dpL x (IMPL k z y) w F.∘ F.equivalence resPL resLP
    dpL (PROD2 k x y) z w = dpL y (IMPR k x z) w F.∘ F.equivalence resPR resRP

    dpR : ∀ {p} (x : Struct +) (y : StructContext p -) (w : Struct p)
        → (NL x ⊢ y [ w ]) ⇔ (NL DPR x y [ w ])
    dpR x (HOLE       ) w = F.id
    dpR x (BOX1  k y  ) w = dpR   (DIA  k x)   y w F.∘ F.equivalence resBD resDB
    dpR x (IMPR1 k y z) w = dpL y (IMPL k z x)   w F.∘ F.equivalence resRL resLR
    dpR x (IMPR2 k y z) w = dpR   (PROD k y x) z w F.∘ F.equivalence resRP resPR
    dpR x (IMPL1 k z y) w = dpR   (PROD k x y) z w F.∘ F.equivalence resLP resPL
    dpR x (IMPL2 k z y) w = dpL y (IMPR k x z)   w F.∘ F.equivalence resLR resRL

  -- `dp1` and `dp2` are helper functions, which allow you to access
  -- the two sides of the isomorphism more easily.
  mutual
    dp1 : ∀ {p} (s : SequentContext p) (w : Struct p) → NL s [ w ] → NL DP s [ w ]
    dp1 s w f = to (dp s w) ⟨$⟩ f

    dp2 : ∀ {p} (s : SequentContext p) (w : Struct p) → NL DP s [ w ] → NL s [ w ]
    dp2 s w f = from (dp s w) ⟨$⟩ f



  -- ** Structuralising Types

  -- Because each logical connective has a structural equivalent, it
  -- is possible -- to a certain extend -- structuralise logical
  -- connectives en masse. The function `St` takes a type, and
  -- computes the maximally structuralised version of that type, given
  -- a target polarity `p`.
  St : ∀ {p} → Type → Struct p
  St { _ } (El      a  ) = · El a ·
  St { + } (Dia   k a  ) = DIA  k (St a)
  St { - } (Box   k a  ) = BOX  k (St a)
  St { + } (UnitR k a  ) = PROD k (St a) (UNIT k)
  St { - } (ImpR  k a b) = IMPR k (St a) (St b)
  St { - } (ImpL  k b a) = IMPL k (St b) (St a)
  St { _ } a             = · a ·

  lem-Neg-St : ∀ a → Pol(a) ≡ - → St { + } a ≡ · a ·
  lem-Neg-St (El      a)   n = refl
  lem-Neg-St (Dia   k a)   ()
  lem-Neg-St (Box   k a)   n = refl
  lem-Neg-St (a & b)       ()
  lem-Neg-St (UnitR k a)   ()
  lem-Neg-St (ImpR  k a b) n = refl
  lem-Neg-St (ImpL  k b a) n = refl

  lem-Pos-St : ∀ a → Pol(a) ≡ + → St { - } a ≡ · a ·
  lem-Pos-St (El      a)   p = refl
  lem-Pos-St (Dia   k a)   p = refl
  lem-Pos-St (Box   k a)   ()
  lem-Pos-St (a & b)       p = refl
  lem-Pos-St (UnitR k a)   p = refl
  lem-Pos-St (ImpR  k a b) ()
  lem-Pos-St (ImpL  k b a) ()

  mutual
    st : ∀ {a b} → NL St a ⊢ St b → NL · a · ⊢ · b ·
    st f = stL (stR f)

    stL : ∀ {a y} → NL St a ⊢ y → NL · a · ⊢ y
    stL {a = El      a  } f = f
    stL {a = Dia   k a  } f = diaL (resBD (stL (resDB f)))
    stL {a = Box   k a  } f = f
    stL {a = a & b}       f = f
    stL {a = UnitR k a  } f = unitRL (resLP (stL (resPL f)))
    stL {a = ImpR  k a b} f = f
    stL {a = ImpL  k b a} f = f

    stR : ∀ {x b} → NL x ⊢ St b → NL x ⊢ · b ·
    stR {b = El      a  } f = f
    stR {b = Dia   k a  } f = f
    stR {b = Box   k a  } f = boxR (resDB (stR (resBD f)))
    stR {b = a & b}       f = f
    stR {b = UnitR k a  } f = f
    stR {b = ImpR  k a b} f = impRR (resPR (stR (resLP (stL (resPL (resRP f))))))
    stR {b = ImpL  k b a} f = impLR (resPL (stR (resRP (stL (resPR (resLP f))))))



  -- ** Identity Expansion

  mutual
    axR : ∀ {b} → NL St b ⊢[ b ]
    axR {b} with Pol(b) | inspect Pol(b)
    ... | + | P.[ p ] = axR' p
    ... | - | P.[ n ] rewrite lem-Neg-St b n = unfR n (stR (focL n (axL' n)))

    axL : ∀ {a} → NL [ a ]⊢ St a
    axL {a} with Pol(a) | inspect Pol(a)
    ... | + | P.[ p ] rewrite lem-Pos-St a p = unfL p (stL (focR p (axR' p)))
    ... | - | P.[ n ] = axL' n

    axR' : ∀ {b} → Pol(b) ≡ + → NL St b ⊢[ b ]
    axR' {El      a}   p = axElR p
    axR' {Dia   x a}   _ = diaR axR
    axR' {Box   x a}   ()
    axR' {a & b}       _ = withR (stR (withL1 axL)) (stR (withL2 axL))
    axR' {UnitR x a}   _ = unitRR axR
    axR' {ImpR  x a b} ()
    axR' {ImpL  x b a} ()

    axL' : ∀ {a} → Pol(a) ≡ - → NL [ a ]⊢ St a
    axL' {El      a}   n = axElL n
    axL' {Dia   x a}   ()
    axL' {Box   x a}   _ = boxL axL
    axL' {a & b}       ()
    axL' {UnitR x a}   ()
    axL' {ImpR  x a b} _ = impRL axR axL
    axL' {ImpL  x b a} _ = impLL axR axL

  ax : ∀ {a} → NL · a · ⊢ · a ·
  ax {a} with Pol(a) | inspect Pol(a)
  ... | + | P.[ p ] rewrite lem-Pos-St a p = stL (focR p (axR' p))
  ... | - | P.[ n ] rewrite lem-Neg-St a n = stR (focL n (axL' n))



  -- ** Quantifier Raising

  -- *** Contexts for Quantifier Raising

  data QRContext (p : Polarity) : Polarity → Set where
    HOLE  : QRContext p p
    PROD1 : QRContext p + → Struct      + → QRContext p +
    PROD2 : Struct      + → QRContext p + → QRContext p +

  instance
    Pluggable-QR : Pluggable (flip QRContext +) Struct (Struct +)
    Pluggable-QR = record { _[_] = _[_]′ }
      where
        _[_]′ : ∀ {p1 p2} → QRContext p1 p2 → Struct p1 → Struct p2
        (HOLE     ) [ z ]′ = z
        (PROD1 x y) [ z ]′ = PROD Sol   (x [ z ]′) y
        (PROD2 x y) [ z ]′ = PROD Sol x (y [ z ]′)

  Trace : QRContext + + → Struct +
  Trace HOLE        = UNIT Hol
  Trace (PROD1 x y) = PROD Sol (PROD Sol C (Trace x)) y
  Trace (PROD2 x y) = PROD Sol (PROD Sol B x) (Trace y)

  up : ∀ x {y z} → NL x [ y ] ⊢ z → NL y ∘ Trace x ⊢ z
  up HOLE        f = unitRI f
  up (PROD1 x y) f = upC (resLP (up x (resPL f)))
  up (PROD2 x y) f = upB (resRP (up y (resPR f)))

  down : ∀ x {a z} → NL · a · ∘ Trace x ⊢ z → NL x [ · Q a · ] ⊢ z
  down x f = init x (move x f)
    where
    init : ∀ (x : QRContext + +) {a z} → NL x [ · a · ∘ I ] ⊢ z → NL x [ · Q a · ] ⊢ z
    init HOLE        f = unitRL f
    init (PROD1 x y) f = resLP (init x (resPL f))
    init (PROD2 x y) f = resRP (init y (resPR f))
    move : ∀ (x : QRContext + +) {y z} → NL y ∘ Trace x ⊢ z → NL x [ y ∘ I ] ⊢ z
    move HOLE        f = f
    move (PROD1 x y) f = resLP (move x (resPL (dnC f)))
    move (PROD2 x y) f = resRP (move y (resPR (dnB f)))

  qrL : ∀ x {y b c} → NL Trace x ⊢[ b ] → NL [ c ]⊢ y → NL x [ · Q (c ⇦ b) · ] ⊢ y
  qrL x f g = down x (resLP (focL refl (impLL f g)))

  qrR : ∀ x {a b} → NL x [ · a · ] ⊢ · b · → NL Trace x ⊢ · a ⇨ b ·
  qrR x f = impRR (resPR (up x f))


module Example where

  open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)

  module Atom where
  {- -}
    data Atom : Set where
      S   : Atom
      N   : Atom
      NP  : Atom
      INF : Atom
  {- -}
  open Atom using (Atom)

  PolarisedAtom : Polarised Atom
  PolarisedAtom = record { Pol = λ{ _ → - } }

  open Syn Atom PolarisedAtom

  pattern S   = El Atom.S
  pattern N   = El Atom.N
  pattern NP  = El Atom.NP
  pattern INF = El Atom.INF
  pattern IV  = NP ⇒ S
  pattern TV  = IV ⇐ NP

  mary   = ·_· {+} (NP)
  bill   = ·_· {+} (NP)
  wants  = ·_· {+} ((IV ⇐ INF) & ((IV ⇐ INF) ⇐ NP))
  to     = ·_· {+} (INF ⇐ IV)
  leave  = ·_· {+} (IV)
  reads  = ·_· {+} (TV)
  a      = ·_· {+} (Q (S ⇦ (NP ⇨ S)) ⇐ N)
  book   = ·_· {+} (N)
  the    = ·_· {+} (NP ⇐ N)
  author = ·_· {+} (N)
  of     = ·_· {+} ((N ⇒ N) ⇐ NP)
  which  = ·_· {+} (Q (((N ⇒ N) ⇐ (S ⇂ NP)) ⇦ (NP ⇨ NP)))
  john   = ·_· {+} (NP)
  likes  = ·_· {+} (TV)


  prf1 : NL (mary ∙ reads ∙ a ∙ book ∙ (the ∙ author ∙ of ∙ which) ∙ john ∙ likes ⊢ · S ·)
  prf1 =
    (resRP (resRP (resLP (focL refl (impLL
    (unfR refl (resRP (resLP
    (qrL (PROD2 _ (PROD2 _ (PROD2 _ HOLE))) (unfR refl
    (qrR (PROD2 _ (PROD2 _ (PROD2 _ HOLE))) (resLP (focL refl
    (impLL (unfR refl (resRP (resLP (focL refl axL)))) axL)))))
    (impLL (unfR refl (impLR (resPL (resRP (diaL (resPR (extRR
    (resRP (resLP (focL refl (impLL (unfR refl (resBD (focL refl
    (boxL axL)))) axL))))))))))) axL)))))
    (unfL refl (resPR (resPR
    (qrL (PROD2 _ (PROD2 _ HOLE)) (unfR refl
    (qrR (PROD2 _ (PROD2 _ HOLE)) (resRP (resLP (focL refl axL))))) axL))))
    )))))

  prf2A : NL (mary ∙ wants ∙ to ∙ leave ⊢ · S ·)
  prf2A = resRP {!!}

-- -}
-- -}
-- -}
-- -}
-- -}
