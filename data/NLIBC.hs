{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
module NLIBC where


import           Prelude         hiding (pred,read,reads)
import           Data.List       (nub)
import           NLIBC.Syntax    hiding (Q,T,S,N,NP,PP,INF)
import qualified NLIBC.Syntax    as Syn
import           NLIBC.Semantics (HI,H,E,T,v0,v1,v2,v3,v4,Sem(..))
import qualified NLIBC.Semantics as Sem
import           NLIBC.Semantics.Show1
import           NLIBC.Semantics.Show2


-- This file contains example sentences treated with my extension of
-- NLIBC, which is capable of expressing quantifiers, scope islands,
-- infixation and extraction.
--
-- The `findAll` statements will search for proofs in the grammar
-- logic for the given sequent, which can then be interpreted
-- semantically using the `eta` function.
--
-- For purposes of presentation, the `show2` function is applied,
-- which -- when given some lambda term representations for the words
-- in the sentence -- will compute the sentence representation. This
-- means that the sentence meaning is converted to normal-form, the
-- word meanings are inserted in the appropriate places, and
-- quantifiers and such are resolved. Keep in mind, though, that this
-- step is only there to get a string representation of the term, and
-- that the sentence meaning can be anything that forms a simply-typed
-- lambda calculus with products and units.
--
-- Note: the notation used for lambda terms is based on the one used
-- in formal semantics. The most confusing feature is the fact that
-- the application of a postulate -- e.g. person -- is written in the
-- traditional mathematical style -- i.e. person(x) -- whereas the
-- application of a composite function is written in functional
-- style. Additionally, the calculus has some syntactic sugar for the
-- quantifiers -- ∀x.u abbreviates ∀(λx.u) and likewise for ∃ -- and
-- is extended with postulates for the logical connectives.

eng0  = show2 (Pair john runs)
        <$> findAll (JOHN ∙ RUNS ⊢ S)
        -- 1
        -- run(john)

eng1  = show2 (Pair john (Pair likes mary))
        <$> findAll (JOHN ∙ LIKES ∙ MARY ⊢ S)
        -- 1
        -- like(john,mary)

eng2  = show2 (Pair someone (Pair likes mary))
        <$> findAll (SOMEONE ∙ LIKES ∙ MARY ⊢ S)
        -- 1
        -- ∃x30.person(x30) ∧ like(x30,mary)

eng3  = show2 (Pair john (Pair likes everyone))
        <$> findAll (JOHN ∙ LIKES ∙ EVERYONE ⊢ S)
        -- 1
        -- ∀x43.person(x43) ⊃ like(john,x43)

eng4  = show2 (Pair someone (Pair likes everyone))
        <$> findAll (SOMEONE ∙ LIKES ∙ EVERYONE ⊢ S)
        -- 2
        -- ∃x60.person(x60) ∧ (∀x64.person(x64) ⊃ like(x60,x64))
        -- ∀x64.person(x64) ⊃ (∃x60.person(x60) ∧ like(x60,x64))

eng5  = show2 (Pair (Pair the waiter) (Pair serves everyone))
        <$> findAll ((THE ∙ WAITER) ∙ SERVES ∙ EVERYONE ⊢ S)
        -- 3
        -- ∀x50.person(x50) ⊃ serve(the(waiter),x50)
        -- ∀x53.person(x53) ⊃ serve(the(waiter),x53)
        -- ∀x50.person(x50) ⊃ serve(the(waiter),x50)

eng6  = show2 (Pair (Pair the (Pair same waiter)) (Pair serves everyone))
       <$> findAll ((THE ∙ SAME ∙ WAITER) ∙ SERVES ∙ EVERYONE ⊢ S)
        -- 6
        -- ∃x157.(∀x166.person(x166) ⊃ serve(the(λx161.waiter(x161) ∧ x161 ≡ x157),x166))
        -- ∃x154.(∀x163.person(x163) ⊃ serve(the(λx158.waiter(x158) ∧ x158 ≡ x154),x163))
        -- ∃x151.(∀x160.person(x160) ⊃ serve(the(λx155.waiter(x155) ∧ x155 ≡ x151),x160))
        -- ∃x154.(∀x163.person(x163) ⊃ serve(the(λx158.waiter(x158) ∧ x158 ≡ x154),x163))
        -- ∃x151.(∀x160.person(x160) ⊃ serve(the(λx155.waiter(x155) ∧ x155 ≡ x151),x160))
        -- ∃x148.(∀x157.person(x157) ⊃ serve(the(λx152.waiter(x152) ∧ x152 ≡ x148),x157))

eng7  = show2 (Pair (Pair some (Pair different waiter)) (Pair serves everyone))
       <$> findAll ((SOME ∙ DIFFERENT ∙ WAITER) ∙ SERVES ∙ EVERYONE ⊢ S)
        -- 6
        -- ∃x1.(∀x2.(∀x3.¬(∃x4.x1(x2,x4) ∧ x1(x3,x4)))) ∧ (∀x5.person(x5) ⊃ (∃x6.waiter(x6) ∧ x1(x6,x5) ∧ serve(x6,x5)))
        -- ∃x1.(∀x2.(∀x3.¬(∃x4.x1(x2,x4) ∧ x1(x3,x4)))) ∧ (∀x5.person(x5) ⊃ (∃x6.waiter(x6) ∧ x1(x6,x5) ∧ serve(x6,x5)))
        -- ∃x1.(∀x2.(∀x3.¬(∃x4.x1(x2,x4) ∧ x1(x3,x4)))) ∧ (∀x5.person(x5) ⊃ (∃x6.waiter(x6) ∧ x1(x6,x5) ∧ serve(x6,x5)))
        -- ∃x1.(∀x2.(∀x3.¬(∃x4.x1(x2,x4) ∧ x1(x3,x4)))) ∧ (∀x5.person(x5) ⊃ (∃x6.waiter(x6) ∧ x1(x6,x5) ∧ serve(x6,x5)))
        -- ∃x1.(∀x2.(∀x3.¬(∃x4.x1(x2,x4) ∧ x1(x3,x4)))) ∧ (∀x5.person(x5) ⊃ (∃x6.waiter(x6) ∧ x1(x6,x5) ∧ serve(x6,x5)))
        -- ∃x1.(∀x2.(∀x3.¬(∃x4.x1(x2,x4) ∧ x1(x3,x4)))) ∧ (∀x5.person(x5) ⊃ (∃x6.waiter(x6) ∧ x1(x6,x5) ∧ serve(x6,x5)))

eng8  = show2 (Pair mary (Pair wants (Pair to leave)))
        <$> findAll (MARY ∙ WANTS ∙ (TO ∙ LEAVE) ⊢ S)
        -- 2
        -- want(mary,leave(mary))
        -- want(mary,leave(mary))

eng9  = show2 (Pair mary (Pair (Pair wants john) (Pair to leave)))
        <$> findAll (MARY ∙ (WANTS ∙ JOHN) ∙ (TO ∙ LEAVE) ⊢ S)
        -- 2
        -- want(mary,leave(john))
        -- want(mary,leave(john))

eng10 = show2 (Pair mary (Pair (Pair wants everyone) (Pair to leave)))
        <$> findAll (MARY ∙ (WANTS ∙ EVERYONE) ∙ (TO ∙ LEAVE) ⊢ S)
        -- 6
        -- ∀x72.person(x72) ⊃ want(mary,leave(x72))
        -- ∀x75.person(x75) ⊃ want(mary,leave(x75))
        -- ∀x72.person(x72) ⊃ want(mary,leave(x72))
        -- ∀x75.person(x75) ⊃ want(mary,leave(x75))
        -- ∀x69.person(x69) ⊃ want(mary,leave(x69))
        -- ∀x72.person(x72) ⊃ want(mary,leave(x72))

eng11 = show2 (Pair mary (Pair wants (Pair to (Pair like bill))))
        <$> findAll (MARY ∙ WANTS ∙ TO ∙ LIKE ∙ BILL ⊢ S)
        -- 2
        -- want(mary,like(mary,bill))
        -- want(mary,like(mary,bill))

eng12 = show2 (Pair mary (Pair (Pair wants john) (Pair to (Pair like bill))))
        <$> findAll (MARY ∙ (WANTS ∙ JOHN) ∙ TO ∙ LIKE ∙ BILL ⊢ S)
        -- 2
        -- want(mary,like(john,bill))
        -- want(mary,like(john,bill))

eng13 = show2 (Pair mary (Pair (Pair wants everyone) (Pair to (Pair like bill))))
        <$> findAll (MARY ∙ (WANTS ∙ EVERYONE) ∙ TO ∙ LIKE ∙ BILL ⊢ S)
        -- 6
        -- ∀x79.person(x79) ⊃ want(mary,like(x79,bill))
        -- ∀x76.person(x76) ⊃ want(mary,like(x76,bill))
        -- ∀x79.person(x79) ⊃ want(mary,like(x79,bill))
        -- ∀x76.person(x76) ⊃ want(mary,like(x76,bill))
        -- ∀x76.person(x76) ⊃ want(mary,like(x76,bill))
        -- ∀x73.person(x73) ⊃ want(mary,like(x73,bill))

eng14 = show2 (Pair mary (Pair wants (Pair to (Pair like someone))))
        <$> findAll (MARY ∙ WANTS ∙ TO ∙ LIKE ∙ SOMEONE ⊢ S)
        -- 3
        -- want(mary,∃x67.person(x67) ∧ like(mary,x67))
        -- ∃x86.person(x86) ∧ want(mary,like(mary,x86))
        -- ∃x83.person(x83) ∧ want(mary,like(mary,x83))

eng15 = show2 (Pair mary (Pair (Pair wants john) (Pair to (Pair like someone))))
        <$> findAll (MARY ∙ (WANTS ∙ JOHN) ∙ TO ∙ LIKE ∙ SOMEONE ⊢ S)
        -- 3
        -- want(mary,∃x71.person(x71) ∧ like(john,x71))
        -- ∃x90.person(x90) ∧ want(mary,like(john,x90))
        -- ∃x87.person(x87) ∧ want(mary,like(john,x87))

eng16 = show2 (Pair mary (Pair (Pair wants everyone) (Pair to (Pair like someone))))
        <$> findAll (MARY ∙ (WANTS ∙ EVERYONE) ∙ TO ∙ LIKE ∙ SOMEONE ⊢ S)
        -- 11
        -- ∀x112.person(x112) ⊃ want(mary,∃x117.person(x117) ∧ like(x112,x117))
        -- ∀x112.person(x112) ⊃ want(mary,∃x117.person(x117) ∧ like(x112,x117))
        -- ∀x109.person(x109) ⊃ want(mary,∃x114.person(x114) ∧ like(x109,x114))
        -- ∀x128.person(x128) ⊃ (∃x133.person(x133) ∧ want(mary,like(x128,x133)))
        -- ∀x125.person(x125) ⊃ (∃x130.person(x130) ∧ want(mary,like(x125,x130)))
        -- ∃x136.person(x136) ∧ (∀x131.person(x131) ⊃ want(mary,like(x131,x136)))
        -- ∃x133.person(x133) ∧ (∀x128.person(x128) ⊃ want(mary,like(x128,x133)))
        -- ∃x136.person(x136) ∧ (∀x131.person(x131) ⊃ want(mary,like(x131,x136)))
        -- ∃x133.person(x133) ∧ (∀x128.person(x128) ⊃ want(mary,like(x128,x133)))
        -- ∃x133.person(x133) ∧ (∀x128.person(x128) ⊃ want(mary,like(x128,x133)))
        -- ∃x130.person(x130) ∧ (∀x125.person(x125) ⊃ want(mary,like(x125,x130)))

eng17 = show2 (Pair mary (Pair says (Pair john (Pair likes bill))))
        <$> findAll (MARY ∙ SAYS ∙ (SDIA SReset (JOHN ∙ LIKES ∙ BILL)) ⊢ S)
        -- 1
        -- say(mary,like(john,bill))

eng18 = show2 (Pair mary (Pair says (Pair everyone (Pair likes bill))))
        <$> findAll (MARY ∙ SAYS ∙ (SDIA SReset (EVERYONE ∙ LIKES ∙ BILL)) ⊢ S)
        -- 1
        -- say(mary,∀x40.person(x40) ⊃ like(x40,bill))

eng19 = show2 (Pair mary (Pair reads (Pair some (Pair book (Pair
              (Pair the (Pair author (Pair of' which))) (Pair john likes))))))
        <$> findAll (MARY ∙ READ ∙ SOME ∙ BOOK ∙ (THE ∙ AUTHOR ∙ OF ∙ WHICH) ∙ (JOHN ∙ LIKES) ⊢ S)
        -- 1
        -- ∃x148.book(x148) ∧ like(john,the(of(x148,author))) ∧ read(mary,x148)

eng20 = show2 (Pair mary (Pair sees (Pair some fox)))
        <$> findAll (MARY ∙ SEES ∙ SOME ∙ FOX ⊢ S)
        -- 1
        -- ∃x1.fox(x1) ∧ see(mary,x1)

eng21 = show2 (Pair mary (Pair sees foxes))
        <$> findAll (MARY ∙ SEES ∙ FOXES ⊢ S)
        -- 1
        -- ∃x1.(∃x2.(∃x3.x1(x2) ∧ x1(x3) ∧ ¬(x2 ≡ x3))) ∧ (∀x4.x1(x4) ⊃ (fox(x4) ∧ see(mary,x4)))


-- -}
-- -}
-- -}
-- -}
-- -}

not_empty :: Repr ts ((E -> T) -> T)
not_empty = Abs (Exists (App v1 v0))

more_than_one :: Repr ts ((E -> T) -> T)
more_than_one = Abs (Exists (Exists ((App v2 v1 :∧ App v2 v0) :∧ (v1 :≢ v0))))

john       = Con "john"                               :: Repr ts (H JOHN)
mary       = Con "mary"                               :: Repr ts (H MARY)
bill       = Con "bill"                               :: Repr ts (H BILL)
run        = Con "run"                                :: Repr ts (H RUN)   ; runs   = run
leave      = Con "leave"                              :: Repr ts (H LEAVE) ; leaves = leave
read       = transitiveVerb "read"                    :: Repr ts (H LIKE)  ; reads  = read
see        = transitiveVerb "see"                     :: Repr ts (H LIKE)  ; sees   = see
like       = transitiveVerb "like"                    :: Repr ts (H LIKE)  ; likes  = like
serve      = transitiveVerb "serve"                   :: Repr ts (H SERVE) ; serves = serve
say        = transitiveVerb "say"                     :: Repr ts (H SAY)   ; says   = say
want       = Pair want1 want2                         :: Repr ts (H WANT)
  where
  want1    = (Abs (Abs (     Con "want" `App` v0 `App` (v1 `App` v0) )))
  want2    = (Abs (Abs (Abs (Con "want" `App` v0 `App` (v1 `App` v2)))))
wants      = want
the        = Con "the"                                :: Repr ts (H THE)
to         = Abs v0                                   :: Repr ts (H TO)
same       = Pair same1 Top                           :: Repr ts (H SAME)
  where
  same1    = Abs (Exists (App v1 (Pair (Abs (Abs (App (App v1 (
             Abs (Abs (App v1 v0 :∧ (v0 :≡ v4))))) v0))) Top)))
different  = Pair diff1 Top                           :: Repr ts (H SAME)
  where
  cond1    = Forall (Forall (Not (Exists (App (App v3 v2) v0 :∧ App (App v3 v1) v0))))
  diff1    = Abs (Exists (cond1 :∧ (App v1 (Pair (Abs (Abs (App (App v1 (
             Abs (Abs (App v1 v0 :∧ (App (App v4 v0) v2))))) v0))) Top))))
waiter     = Con "waiter"                             :: Repr ts (H WAITER)
fox        = Con "fox"                                :: Repr ts (H FOX)
foxes      = Pair foxes1 Top                          :: Repr ts (H FOXES)
  where
    foxes1 :: Repr ts ((E -> T) -> T)
    foxes1 = Abs (Exists (App more_than_one v0 :∧
             Forall (App v1 v0 :⊃ (App fox v0 :∧ App v2 v0))))
person     = Con "person"                             :: Repr ts (H PERSON)
book       = Con "book"                               :: Repr ts (H WAITER)
author     = Con "author"                             :: Repr ts (H PERSON)
someone    = App some  person                         :: Repr ts (H SOMEONE)
everyone   = App every person                         :: Repr ts (H EVERYONE)
of'        = Con "of"                                 :: Repr ts (H OF)
which      = Pair (Pair which1 Top) (Pair which1 Top) :: Repr ts (H WHICH)
  where
    which1 :: Repr ts ((E -> E) -> (E -> T) -> (E -> T) -> E -> T)
    which1 = Abs (Abs (Abs (Abs (App v1 v0 :∧ App v2 (App v3 v0)))))
some       = Abs (Pair (Abs (Exists ((App v2 v0) :∧ (App v1 v0)))) Top)
every      = Abs (Pair (Abs (Forall ((App v2 v0) :⊃ (App v1 v0)))) Top)


transitiveVerb n = Abs (Abs (App (App (Con n) v0) v1))


-- -}
-- -}
-- -}
-- -}
-- -}


type    S       = El 'Syn.S
type    N       = El 'Syn.N
type    NP      = El 'Syn.NP
type    PP      = El 'Syn.PP
type    INF     = El 'Syn.INF
type    NP'S    = NP :⇨ S
type    A       = N :← N
type    IV      = NP :→ S
type    TV      = (NP :→ S) :← NP
type    DET     = NP :← N
type    Q a b c = UnitR Hollow (c :⇦ (a :⇨ b))
pattern S       = SEl SS
pattern N       = SEl SN
pattern NP      = SEl SNP
pattern NP'S    = NP :%⇨ S
pattern PP      = SEl SPP
pattern INF     = SEl SINF
pattern A       = SEl SN :%← SEl SN
pattern IV      = SEl SNP :%→ SEl SS
pattern TV      = (SEl SNP :%→ SEl SS) :%← SEl SNP
pattern DET     = SEl SNP :%← SEl SN
pattern Q a b c = SUnitR SHollow (c :%⇦ (a :%⇨ b))


type    JOHN      = NP
type    MARY      = NP
type    BILL      = NP
type    RUN       = IV                                     ; type    RUNS   = RUN
type    LIKE      = TV                                     ; type    LIKES  = LIKE
type    SEE       = TV                                     ; type    SEES  = SEE
type    SERVE     = TV                                     ; type    SERVES = SERVE
type    WANT      = (IV :← INF) :& ((IV :← INF) :← NP)     ; type    WANTS  = WANT
type    LEAVE     = IV                                     ; type    LEAVES = LEAVE
type    SAY       = IV :← Dia Reset S                      ; type    SAYS   = SAY
type    THE       = DET
type    TO        = INF :← IV
type    SAME      = Q (Q A NP'S NP'S) S S
type    DIFFERENT = Q (Q A NP'S NP'S) S S
type    WAITER    = N
type    FOX       = N
type    FOXES     = Q NP S S
type    PERSON    = N
type    BOOK      = N
type    AUTHOR    = N
type    SOME      = Q NP S S :← N
type    EVERY     = Q NP S S :← N
type    SOMEONE   = Q NP S S
type    EVERYONE  = Q NP S S
type    OF        = (N :→ N) :← NP
type    WHICH     = (Q NP NP ((N :→ N) :← (S :⇂ NP))) :& (Q NP NP ((N :→ N) :← (NP :→ S)))
pattern JOHN      = NP
pattern MARY      = NP
pattern BILL      = NP
pattern READ      = TV                                     ; pattern READS  = READ
pattern RUN       = IV                                     ; pattern RUNS   = RUN
pattern LIKE      = TV                                     ; pattern LIKES  = LIKE
pattern SEE       = TV                                     ; pattern SEES  = SEE
pattern SERVE     = TV                                     ; pattern SERVES = SERVE
pattern WANT      = (IV :%← INF) :%& ((IV :%← INF) :%← NP) ; pattern WANTS  = WANT
pattern LEAVE     = IV                                     ; pattern LEAVES = LEAVE
pattern SAY       = IV :%← SDia SReset S                   ; pattern SAYS   = SAY
pattern THE       = DET
pattern TO        = INF :%← IV
pattern SAME      = Q (Q A NP'S NP'S) S S
pattern DIFFERENT = Q (Q A NP'S NP'S) S S
pattern WAITER    = N
pattern FOX       = N
pattern FOXES     = Q NP S S
pattern PERSON    = N
pattern BOOK      = N
pattern AUTHOR    = N
pattern SOME      = Q NP S S :%← N
pattern EVERY     = Q NP S S :%← N
pattern SOMEONE   = Q NP S S
pattern EVERYONE  = Q NP S S
pattern OF        = (N :%→ N) :%← NP
pattern WHICH     = (Q NP NP ((N :%→ N) :%← (S :%⇂ NP))) :%& (Q NP NP ((N :%→ N) :%← (NP :%→ S)))


pattern Forall u = App (Con "∀") (Abs u)
pattern Exists u = App (Con "∃") (Abs u)
pattern Not  x = App (Con "¬") x
pattern x :∧ y = App (App (Con "∧") x) y
pattern x :⊃ y = App (App (Con "⊃") x) y
pattern x :≡ y = App (App (Con "≡") x) y
pattern x :≢ y = Not (App (App (Con "≡") x) y)
