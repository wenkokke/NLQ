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
  lem-Neg-St (UnitR k a)   ()
  lem-Neg-St (ImpR  k a b) n = refl
  lem-Neg-St (ImpL  k b a) n = refl

  lem-Pos-St : ∀ a → Pol(a) ≡ + → St { - } a ≡ · a ·
  lem-Pos-St (El      a)   p = refl
  lem-Pos-St (Dia   k a)   p = refl
  lem-Pos-St (Box   k a)   ()
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
    stL {a = UnitR k a  } f = unitRL (resLP (stL (resPL f)))
    stL {a = ImpR  k a b} f = f
    stL {a = ImpL  k b a} f = f

    stR : ∀ {x b} → NL x ⊢ St b → NL x ⊢ · b ·
    stR {b = El      a  } f = f
    stR {b = Dia   k a  } f = f
    stR {b = Box   k a  } f = boxR (resDB (stR (resBD f)))
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
    axR' {Dia   x a}   p = diaR axR
    axR' {Box   x a}   ()
    axR' {UnitR x a}   p = unitRR axR
    axR' {ImpR  x a b} ()
    axR' {ImpL  x b a} ()

    axL' : ∀ {a} → Pol(a) ≡ - → NL [ a ]⊢ St a
    axL' {El      a}   n = axElL n
    axL' {Dia   x a}   ()
    axL' {Box   x a}   n = boxL axL
    axL' {UnitR x a}   ()
    axL' {ImpR  x a b} n = impRL axR axL
    axL' {ImpL  x b a} n = impLL axR axL

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
      S  : Atom
      N  : Atom
      NP : Atom
  {- -}
  open Atom using (Atom)

  PolarisedAtom : Polarised Atom
  PolarisedAtom = record { Pol = λ{ _ → - } }

  open Syn Atom PolarisedAtom

  pattern S  = El Atom.S
  pattern N  = El Atom.N
  pattern NP = El Atom.NP

  mary   = ·_· {+} (NP)
  reads  = ·_· {+} ((NP ⇒ S) ⇐ NP)
  a      = ·_· {+} (Q (S ⇦ (NP ⇨ S)) ⇐ N)
  book   = ·_· {+} (N)
  the    = ·_· {+} (NP ⇐ N)
  author = ·_· {+} (N)
  of     = ·_· {+} ((N ⇒ N) ⇐ NP)
  which  = ·_· {+} (Q (((N ⇒ N) ⇐ (S ⇂ NP)) ⇦ (NP ⇨ NP)))
  john   = ·_· {+} (NP)
  likes  = ·_· {+} ((NP ⇒ S) ⇐ NP)

  prf : NL (mary ∙ reads ∙ a ∙ book ∙ (the ∙ author ∙ of ∙ which) ∙ john ∙ likes ⊢ · S ·)
  prf =
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

  {-
  (resRP (resRP (resLP (focL refl (impLL
      (unfR refl (resRP (resLP
        (qrL (PROD2 _ (PROD2 _ (PROD2 _ HOLE))) (unfR refl
        (qrR (PROD2 _ (PROD2 _ (PROD2 _ HOLE))) (resLP (focL refl
          (impLL (unfR refl (resRP (resLP (focL refl axL)))) axL)))))
        (impLL (unfR refl (impLR (resPL (resRP (diaL (resPR (ifxRR
        (resRP (resLP (focL refl (impLL (unfR refl (resBD (focL refl
        (boxL axL)))) axL))))))))))) axL)))))
      (unfL refl (resPR (resPR
        (qrL (PROD2 _ (PROD2 _ HOLE)) (unfR refl
        (qrR (PROD2 _ (PROD2 _ HOLE)) (resRP (resLP (focL refl axL))))) axL))))
    )))))
  -}

{-
module SynToAgda
  (Atom : Set)
  (PolarisedAtom : Polarised Atom)
  (TranslateAtom : Translate Atom Set)
  where


  open import Function     using (id; flip; _∘_)
  open import Data.Unit    using (⊤; tt)
  open import Data.Product using (_×_; _,_)
  open module ISyn = Syn Atom PolarisedAtom hiding (_∘_)


  instance
    TranslateType : Translate NL.Type Set
    TranslateType = record { _* = _*′ }
      where
        _*′ : NL.Type → Set
        El      a   *′ = a *
        Dia   _ a   *′ = a *′
        Box   _ a   *′ = a *′
        UnitR _ a   *′ = a *′
        ImpR  _ a b *′ = a *′ → b *′
        ImpL  _ b a *′ = a *′ → b *′

    TranslateStruct : ∀ {p} → Translate (NL.Struct p) Set
    TranslateStruct = record { _* = _*′ }
      where
        _*′ : ∀ {p} → NL.Struct p → Set
        · a ·      *′ = a *
        B          *′ = ⊤
        C          *′ = ⊤
        DIA  _ x   *′ = x *′
        UNIT _     *′ = ⊤
        PROD _ x y *′ = x *′ × y *′
        BOX  _ x   *′ = x *′
        IMPR _ x y *′ = x *′ → y *′
        IMPL _ y x *′ = x *′ → y *′

    TranslateSequent : Translate NL.Sequent Set
    TranslateSequent = record { _* = _*′ }
      where
        _*′ : NL.Sequent → Set
        (  x  ⊢  y  ) *′ = x * → y *
        ([ a ]⊢  y  ) *′ = a * → y *
        (  x  ⊢[ b ]) *′ = x * → b *

    TranslateProof : ∀ {s} → Translate (NL s) (s *)
    TranslateProof = record { _* = _*′ }
      where
        _*′ : ∀ {s} → NL s → s *
        axElR _     *′ = id
        axElL _     *′ = id
        unfR  _ f   *′ = f *′
        unfL  _ f   *′ = f *′
        focR  _ f   *′ = f *′
        focL  _ f   *′ = f *′
        impRL   f g *′ = λ h → g *′ ∘ h ∘ f *′
        impRR   f   *′ = f *′
        impLL   f g *′ = λ h → g *′ ∘ h ∘ f *′
        impLR   f   *′ = f *′
        resRP   f   *′ = λ{(x , y) → (f *′)  y   x }
        resLP   f   *′ = λ{(x , y) → (f *′)  x   y }
        resPR   f   *′ = λ{ y   x  → (f *′) (x , y)}
        resPL   f   *′ = λ{ x   y  → (f *′) (x , y)}
        unitRL  f   *′ = λ{ x      → (f *′) (x , _)}
        unitRR  f   *′ = λ{(x , _) → (f *′)  x     }
        unitRI  f   *′ = λ{(x , _) → (f *′)  x     }
        diaL    f   *′ = f *′
        diaR    f   *′ = f *′
        boxL    f   *′ = f *′
        boxR    f   *′ = f *′
        resBD   f   *′ = f *′
        resDB   f   *′ = f *′
        upB     f   *′ = λ{( y , (_ , x) , z) → (f *′) ( x ,      y  , z)}
        upC     f   *′ = λ{( x , (_ , y) , z) → (f *′) ((x ,      y) , z)}
        dnB     f   *′ = λ{( x ,      y  , z) → (f *′) ( y , (_ , x) , z)}
        dnC     f   *′ = λ{((x ,      y) , z) → (f *′) ( x , (_ , y) , z)}
        ifxRR   f   *′ = λ{( x , y  , z) → (f *′) ((x , y) , z)}
        ifxLR   f   *′ = λ{((x , z) , y) → (f *′) ((x , y) , z)}
        ifxLL   f   *′ = λ{((z , y) , x) → (f *′) ( z , y  , x)}
        ifxRL   f   *′ = λ{( y , z  , x) → (f *′) ( z , y  , x)}
        extRR   f   *′ = λ{((x , y) , z) → (f *′) ( x , y  , z)}
        extLR   f   *′ = λ{((x , y) , z) → (f *′) ((x , z) , y)}
        extLL   f   *′ = λ{( z , y ,  x) → (f *′) ((z , y) , x)}
        extRL   f   *′ = λ{( z , y ,  x) → (f *′) ( y , z  , x)}


module Sem (Atom : Set) where

  open import Function                                   using (_$_)
  open import Relation.Binary.PropositionalEquality as P using (_≡_; refl; sym; cong)

  infixr 7 _⊗_
  infixr 6 _⇒_
  infixr 5 _∙_ _∙>_
  infixl 5 _<∙_
  infix  6 _[_] _<_>
  infix  2 _⊢_
  infix  1 ILL_

  data Type : Set where
    𝟙   : Type
    El  : Atom → Type
    _⇒_ : Type → Type → Type
    _⊗_ : Type → Type → Type

  data Struct : Set where
    ∅   : Struct
    ·_· : Type   → Struct
    _∙_ : Struct → Struct → Struct

  data Context : Set where
    []   : Context
    _<∙_ : Context → Struct  → Context
    _∙>_ : Struct  → Context → Context

  _[_] : Context → Struct → Struct
  []       [ z ] = z
  (x <∙ y) [ z ] = (x [ z ]) ∙ y
  (x ∙> y) [ z ] = x ∙ (y [ z ])

  _<_> : Context → Context → Context
  []       < z > = z
  (x <∙ y) < z > = (x < z >) <∙ y
  (x ∙> y) < z > = x ∙> (y < z >)

  <>-def : ∀ x y {z} → (x < y >) [ z ] ≡ x [ y [ z ] ]
  <>-def []       y {z}                        = refl
  <>-def (x <∙ _) y {z} rewrite <>-def x y {z} = refl
  <>-def (_ ∙> x) y {z} rewrite <>-def x y {z} = refl

  data Sequent : Set where
    _⊢_ : Struct → Type → Sequent

  data ILL_ : Sequent → Set where
    ax : ∀ {a}         → ILL · a · ⊢ a

    ⇒I : ∀ {x a b}     → ILL x ∙ · a · ⊢ b → ILL x ⊢ a ⇒ b
    ⇒E : ∀ {x y a b}   → ILL x ⊢ a ⇒ b → ILL y ⊢ a → ILL x ∙ y ⊢ b
    ⊗I : ∀ {x y a b}   → ILL x ⊢ a → ILL y ⊢ b → ILL x ∙ y ⊢ a ⊗ b
    ⊗E : ∀ {x y a b c} → ILL x ⊢ a ⊗ b → ILL (· a · ∙ · b ·) ∙ y ⊢ c → ILL x ∙ y ⊢ c
    𝟙I :                 ILL ∅ ⊢ 𝟙
    𝟙E : ∀ {x y c}     → ILL x ⊢ 𝟙 → ILL y ⊢ c → ILL x ∙ y ⊢ c

    ui : ∀ {x c}       → ILL x ∙ ∅ ⊢ c → ILL x ⊢ c
    cm : ∀ {x y c}   w → ILL w [ x ∙ y ] ⊢ c → ILL w [ y ∙ x ] ⊢ c
    a1 : ∀ {x y z c} w → ILL w [ x ∙ (y ∙ z) ] ⊢ c → ILL w [ (x ∙ y) ∙ z ] ⊢ c
    a2 : ∀ {x y z c} w → ILL w [ (x ∙ y) ∙ z ] ⊢ c → ILL w [ x ∙ (y ∙ z) ] ⊢ c

  ue : ∀ {x c} → ILL x ⊢ c → ILL x ∙ ∅ ⊢ c
  ue f = cm [] (𝟙E 𝟙I f)

  ap : ∀ {x a b} → ILL · a · ⊢ b → ILL x ⊢ a → ILL x ⊢ b
  ap f x = ui (cm [] (⇒E (⇒I (cm [] (ue f))) x))

  cf : ∀ {a b c} → ILL · a · ∙ · b · ⊢ c → ILL · a ⊗ b · ⊢ c
  cf f = ui (⊗E ax (ue f))


  -- ** Movement

  data FinalStep : Context → Set where
    []       : FinalStep []
    _<[]<∙_> : ∀ v x → FinalStep (v < [] <∙ x >)
    _<_∙>[]> : ∀ v x → FinalStep (v < x ∙> [] >)

  finalStep : ∀ w → FinalStep w
  finalStep []       = []
  finalStep (w <∙ x) with finalStep w
  finalStep (.[]              <∙ x) | []          = []       <[]<∙ x >
  finalStep (.(v < [] <∙ y >) <∙ x) | v <[]<∙ y > = (v <∙ x) <[]<∙ y >
  finalStep (.(v < y ∙> [] >) <∙ x) | v < y ∙>[]> = (v <∙ x) < y ∙>[]>
  finalStep (x ∙> w) with finalStep w
  finalStep (x ∙> .[])              | []          = []       < x ∙>[]>
  finalStep (x ∙> .(v < [] <∙ y >)) | v <[]<∙ y > = (x ∙> v) <[]<∙ y >
  finalStep (x ∙> .(v < y ∙> [] >)) | v < y ∙>[]> = (x ∙> v) < y ∙>[]>

  rewr : ∀ {x y b} → x ≡ y → ILL x ⊢ b → ILL y ⊢ b
  rewr = P.subst (λ x → ILL x ⊢ _)

  up : ∀ v w {x y a} → ILL v [ x ∙ w [ y ] ] ⊢ a → ILL v [ w [ x ∙ y ] ] ⊢ a
  up v []       {x} {y} {a} f = f
  up v (w <∙ z) {x} {y} {a} f
    = rewr       (<>-def v ([] <∙ z))       $ up (v < [] <∙ z >) w
    $ rewr  (sym (<>-def v ([] <∙ z)))      $ a1 v f
  up v (z ∙> w) {x} {y} {a} f
    = rewr      (<>-def v (z ∙> []))        $ up (v < z ∙> [] >) w
    $ rewr (sym (<>-def v (z ∙> [])))       $ a2 v
    $ rewr      (<>-def v ([] <∙ w [ y ]))  $ cm (v < [] <∙ w [ y ] >)
    $ rewr (sym (<>-def v ([] <∙ w [ y ]))) $ a1 v f

  dn : ∀ v w {x y a} → ILL v [ w [ x ∙ y ] ] ⊢ a → ILL v [ x ∙ w [ y ] ] ⊢ a
  dn v []       {x} {y} {a} f = f
  dn v (w <∙ z) {x} {y} {a} f
    = a2 v                     $ rewr      (<>-def v ([] <∙ z))
    $ dn (v < [] <∙ z >) w     $ rewr (sym (<>-def v ([] <∙ z))) f
  dn v (z ∙> w) {x} {y} {a} f
    = a2 v                     $ rewr      (<>-def v ([] <∙ w [ y ]))
    $ cm (v < [] <∙ w [ y ] >) $ rewr (sym (<>-def v ([] <∙ w [ y ])))
    $ a1 v                     $ rewr      (<>-def v (z ∙> []))
    $ dn (v < z ∙> [] >) w     $ rewr (sym (<>-def v (z ∙> []))) f

  St : Type → Struct
  St (a ⊗ b) = St a ∙ St b
  St    𝟙    = ∅
  St    a    = · a ·

  StAll : Struct → Struct
  StAll (x ∙ y) = StAll x ∙ StAll y
  StAll    ∅    = ∅
  StAll  · a ·  = St a

  mutual
    st : ∀ {a b} w → ILL w [ · a · ] ⊢ b → ILL w [ St a ] ⊢ b
    st {a} w f with finalStep w
    st {a} .[]              f | []
      = ui (stPrv (ue f))
    st {a} .(v < [] <∙ x >) f | v <[]<∙ x >
      = rewr (sym (<>-def v ([] <∙ x)))
      $        up [] v $ stPrv $ dn [] v
      $ rewr (<>-def v ([] <∙ x)) f
    st {a} .(v < x ∙> [] >) f | v < x ∙>[]>
      = rewr (sym (<>-def v (x ∙> [])))
      $ cm v $ up [] v $ stPrv $ dn [] v
      $ cm v $ rewr (<>-def v (x ∙> [])) f

    private
      stPrv : ∀ {a x b} → ILL · a · ∙ x ⊢ b → ILL St a ∙ x ⊢ b
      stPrv {a ⊗ b} f
        = st (([] <∙ _) <∙ _) $ st ((_ ∙> []) <∙ _)
        $ cm [] (⇒E (⇒I (cm [] f)) (⊗I ax ax))
      stPrv {  𝟙  } f = 𝟙E 𝟙I (ui (⇒E (⇒I (cm [] f)) 𝟙I))
      stPrv {El  a} f = f
      stPrv {a ⇒ b} f = f

  stAll : ∀ {x b} w → ILL w [ x ] ⊢ b → ILL w [ StAll x ] ⊢ b
  stAll {  ∅  } w f = f
  stAll {· x ·} w f = st w f
  stAll {x ∙ y} w f
    = rewr (<>-def w ([] <∙ _)) $ stAll (w < [] <∙ _ >) $ rewr (sym (<>-def w ([] <∙ _)))
    $ rewr (<>-def w (_ ∙> [])) $ stAll (w < _ ∙> [] >) $ rewr (sym (<>-def w (_ ∙> []))) f

module SynToSem
  (Atom1 : Set) (PolarisedAtom1 : Polarised Atom1)
  (Atom2 : Set) (Translate-Atom : Translate Atom1 Atom2)
  where


  open module NL = Syn Atom1 PolarisedAtom1 hiding (_∙_; _⇒_; ax)
  open module ISem = Sem Atom2


  instance
    Translate-Type : Translate NL.Type ISem.Type
    Translate-Type = record { _* = _*′ }
      where
        _*′ : NL.Type → ISem.Type
        El      a   *′ = El (a *)
        Dia   _ a   *′ = a *′
        Box   _ a   *′ = a *′
        UnitR _ a   *′ = a *′
        ImpR  _ a b *′ = a *′ ⇒ b *′
        ImpL  _ b a *′ = a *′ ⇒ b *′

    Translate-Struct : ∀ {p} → Translate (NL.Struct p) ISem.Type
    Translate-Struct = record { _* = _*′ }
      where
        _*′ : ∀ {p} → NL.Struct p → ISem.Type
        · a ·      *′ = a *
        B          *′ = 𝟙
        C          *′ = 𝟙
        DIA  _ x   *′ = x *′
        UNIT _     *′ = 𝟙
        PROD _ x y *′ = x *′ ⊗ y *′
        BOX  _ x   *′ = x *′
        IMPR _ x y *′ = x *′ ⇒ y *′
        IMPL _ y x *′ = x *′ ⇒ y *′

    Translate-Sequent : Translate NL.Sequent ISem.Sequent
    Translate-Sequent = record { _* = _*′ }
      where
        _*′ : NL.Sequent → ISem.Sequent
        (  x  ⊢  y  ) *′ = · x * · ⊢ y *
        ([ a ]⊢  y  ) *′ = · a * · ⊢ y *
        (  x  ⊢[ b ]) *′ = · x * · ⊢ b *

    Translate-Proof : ∀ {s} → Translate (NL s) (ILL s *)
    Translate-Proof = record { _* = _*′ }
      where
        _*′ : ∀ {s} → NL s → ILL s *
        axElR _     *′ = ax
        axElL _     *′ = ax
        unfR  _ f   *′ = f *′
        unfL  _ f   *′ = f *′
        focR  _ f   *′ = f *′
        focL  _ f   *′ = f *′

        impRL   f g *′ = ⇒I (ap (g *′) (⇒E ax (f *′)))
        impRR   f   *′ = f *′
        impLL   f g *′ = ⇒I (ap (g *′) (⇒E ax (f *′)))
        impLR   f   *′ = f *′
        resRP   f   *′ = cf (cm [] (⇒E (f *′) ax))
        resLP   f   *′ = cf (      (⇒E (f *′) ax))
        resPR   f   *′ = ⇒I (cm [] (ap (f *′) (⊗I ax ax)))
        resPL   f   *′ = ⇒I (      (ap (f *′) (⊗I ax ax)))

        unitRL  f   *′ = ap (f *′) (ui (⊗I ax 𝟙I))
        unitRR  f   *′ = cf (cm [] (𝟙E ax (f *′)))
        unitRI  f   *′ = cf (cm [] (𝟙E ax (f *′)))

        diaL    f   *′ = f *′
        diaR    f   *′ = f *′
        boxL    f   *′ = f *′
        boxR    f   *′ = f *′
        resBD   f   *′ = f *′
        resDB   f   *′ = f *′

        ifxRR   f   *′ = cf (cm [] (⊗E ax (cm [] (             (a2 [] (ap (f *′) (⊗I (⊗I ax ax) ax)))))))
        ifxLR   f   *′ = cf (      (⊗E ax (a1 [] (cm (_ ∙> []) (a2 [] (ap (f *′) (⊗I (⊗I ax ax) ax)))))))
        ifxLL   f   *′ = cf (      (⊗E ax (a1 [] (             (      (ap (f *′) (⊗I ax (⊗I ax ax))))))))
        ifxRL   f   *′ = cf (cm [] (⊗E ax (a1 [] (cm (_ ∙> []) (      (ap (f *′) (⊗I ax (⊗I ax ax))))))))

        extRR   f   *′ = cf (      (⊗E ax (a1 [] (             (      (ap (f *′) (⊗I ax (⊗I ax ax))))))))
        extLR   f   *′ = cf (      (⊗E ax (a1 [] (cm (_ ∙> []) (a2 [] (ap (f *′) (⊗I (⊗I ax ax) ax)))))))
        extLL   f   *′ = cf (cm [] (⊗E ax (      (cm       []  (a2 [] (ap (f *′) (⊗I (⊗I ax ax) ax)))))))
        extRL   f   *′ = cf (cm [] (⊗E ax (a1 [] (cm (_ ∙> []) (      (ap (f *′) (⊗I ax (⊗I ax ax))))))))

        upB     f   *′ = cf (cm [] (⊗E ax (a1 [] (⊗E ax (a1 [] (𝟙E ax (cm (_ ∙> [])
                         (ap (f *′) (⊗I ax (⊗I ax ax))))))))))
        upC     f   *′ = cf (cm [] (⊗E ax (a1 [] (⊗E ax (a1 [] (𝟙E ax (a2 [] (cm []
                         (a2 [] (ap (f *′) (⊗I (⊗I ax ax) ax)))))))))))
        dnB     f   *′ = cf (cm [] (⊗E ax (a1 [] (ui (a1 [] (a1 (_ ∙> []) (cm (_ ∙> (_ ∙> []))
                         (cm (_ ∙> []) (ap (f *′) (⊗I ax (⊗I (⊗I 𝟙I ax) ax)))))))))))
        dnC     f   *′ = cf (⊗E ax (a1 [] (cm (_ ∙> []) (ui (a1 [] (a1 (_ ∙> [])
                         (cm (_ ∙> (_ ∙> [])) (cm (_ ∙> []) (ap (f *′) (⊗I ax (⊗I (⊗I 𝟙I ax) ax)))))))))))

-- -}
-- -}
-- -}
-- -}
-- -}
