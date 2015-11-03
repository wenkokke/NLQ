{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PatternSynonyms #-}
module NLIBC where


import           Prelude         hiding (pred)
import           Data.List       (nub)
import           NLIBC.Syntax    hiding (Q,T,S,N,NP,PP,INF)
import qualified NLIBC.Syntax    as Syn
import           NLIBC.Semantics (HI,H,E,T,v0,v1,v2,Sem(..))
import qualified NLIBC.Semantics as Sem
import           NLIBC.Semantics.Show1
import           NLIBC.Semantics.Show2


john     = Con "john"                                :: Repr ts (H JOHN)
mary     = Con "mary"                                :: Repr ts (H MARY)
bill     = Con "bill"                                :: Repr ts (H BILL)
run      = Con "run"                                 :: Repr ts (H RUN)   ; runs   = run
leave    = Con "leave"                               :: Repr ts (H LEAVE) ; leaves = leave
like     = Abs (Abs (Con "like"  `App` v0 `App` v1)) :: Repr ts (H LIKE)  ; likes  = like
serve    = Abs (Abs (Con "serve" `App` v0 `App` v1)) :: Repr ts (H SERVE) ; serves = serve
say      = Abs (Abs (Con "say"   `App` v0 `App` v1)) :: Repr ts (H SAY)   ; says   = say
want     = Pair want1 want2                          :: Repr ts (H WANT)
  where
  want1  = (Abs (Abs (     Con "want" `App` v0 `App` (v1 `App` v0) )))
  want2  = (Abs (Abs (Abs (Con "want" `App` v0 `App` (v1 `App` v2)))))
wants    = want
the      = Con "the"                                 :: Repr ts (H THE)
to       = Abs v0                                    :: Repr ts (H TO)
same     = Con "same"                                :: Repr ts (H SAME)
waiter   = Con "waiter"                              :: Repr ts (H WAITER)
person   = Con "person"                              :: Repr ts (H PERSON)
someone  = Pair (Abs (Exists ((App person v0) :∧ (App v1 v0)))) Top
everyone = Pair (Abs (Forall ((App person v0) :⊃ (App v1 v0)))) Top


eng0  = show2 (Pair john runs)
        <$> findAll (NP ∙ IV ⊢ S)
        -- 1
        -- run(john)

eng1  = show2 (Pair john (Pair likes mary))
        <$> findAll (NP ∙ TV ∙ NP ⊢ S)
        -- 1
        -- like(john,mary)

eng2  = show2 (Pair someone (Pair likes mary))
        <$> findAll (Q NP S S ∙ TV ∙ NP ⊢ S)
        -- 1
        -- ∃x30.person(x30) ∧ like(x30,mary)

eng3  = show2 (Pair john (Pair likes everyone))
        <$> findAll (NP ∙ TV ∙ Q NP S S ⊢ S)
        -- 1
        -- ∀x43.person(x43) ⊃ like(john,x43)

eng4  = show2 (Pair someone (Pair likes everyone))
        <$> findAll (Q NP S S ∙ TV ∙ Q NP S S ⊢ S)
        -- 2
        -- ∃x60.person(x60) ∧ (∀x64.person(x64) ⊃ like(x60,x64))
        -- ∀x64.person(x64) ⊃ (∃x60.person(x60) ∧ like(x60,x64))

eng5  = show2 (Pair (Pair the waiter) (Pair serves everyone))
        <$> findAll ((DET ∙ N) ∙ TV ∙ Q NP S S ⊢ S)
        -- 3
        -- ∀x50.person(x50) ⊃ serve(the(waiter),x50)
        -- ∀x53.person(x53) ⊃ serve(the(waiter),x53)
        -- ∀x50.person(x50) ⊃ serve(the(waiter),x50)

eng6  = show2 (Pair (Pair the (Pair same waiter)) (Pair serves everyone))
        <$> findAll ((DET ∙ Q A NP'S NP'S ∙ N) ∙ TV ∙ Q NP S S ⊢ S)
        -- 6
        -- ∀x118.person(x118) ⊃ π₁(same) (λx57.(λx88.serve(the(x57 waiter),x88))) x118
        -- ∀x115.person(x115) ⊃ π₁(same) (λx57.(λx91.serve(the(x57 waiter),x91))) x115
        -- ∀x112.person(x112) ⊃ π₁(same) (λx57.(λx76.serve(the(x57 waiter),x76))) x112
        -- ∀x115.person(x115) ⊃ π₁(same) (λx54.(λx85.serve(the(x54 waiter),x85))) x115
        -- ∀x112.person(x112) ⊃ π₁(same) (λx54.(λx88.serve(the(x54 waiter),x88))) x112
        -- ∀x109.person(x109) ⊃ π₁(same) (λx54.(λx73.serve(the(x54 waiter),x73))) x109

eng7  = show2 (Pair mary (Pair wants (Pair to leave)))
        <$> findAll (MARY ∙ WANTS ∙ (TO ∙ LEAVE) ⊢ S)
        -- 2
        -- want(mary,leave(mary))
        -- want(mary,leave(mary))

eng8  = show2 (Pair mary (Pair (Pair wants john) (Pair to leave)))
        <$> findAll (MARY ∙ (WANTS ∙ JOHN) ∙ (TO ∙ LEAVE) ⊢ S)
        -- 2
        -- want(mary,leave(john))
        -- want(mary,leave(john))

eng9  = show2 (Pair mary (Pair (Pair wants everyone) (Pair to leave)))
        <$> findAll (MARY ∙ (WANTS ∙ EVERYONE) ∙ (TO ∙ LEAVE) ⊢ S)
        -- 6
        -- ∀x72.person(x72) ⊃ want(mary,leave(x72))
        -- ∀x75.person(x75) ⊃ want(mary,leave(x75))
        -- ∀x72.person(x72) ⊃ want(mary,leave(x72))
        -- ∀x75.person(x75) ⊃ want(mary,leave(x75))
        -- ∀x69.person(x69) ⊃ want(mary,leave(x69))
        -- ∀x72.person(x72) ⊃ want(mary,leave(x72))

eng10 = show2 (Pair mary (Pair wants (Pair to (Pair like bill))))
        <$> findAll (MARY ∙ WANTS ∙ TO ∙ LIKE ∙ BILL ⊢ S)
        -- 2
        -- want(mary,like(mary,bill))
        -- want(mary,like(mary,bill))

eng11 = show2 (Pair mary (Pair (Pair wants john) (Pair to (Pair like bill))))
        <$> findAll (MARY ∙ (WANTS ∙ JOHN) ∙ TO ∙ LIKE ∙ BILL ⊢ S)
        -- 2
        -- want(mary,like(john,bill))
        -- want(mary,like(john,bill))

eng12 = show2 (Pair mary (Pair (Pair wants everyone) (Pair to (Pair like bill))))
        <$> findAll (MARY ∙ (WANTS ∙ EVERYONE) ∙ TO ∙ LIKE ∙ BILL ⊢ S)
        -- 6
        -- ∀x79.person(x79) ⊃ want(mary,like(x79,bill))
        -- ∀x76.person(x76) ⊃ want(mary,like(x76,bill))
        -- ∀x79.person(x79) ⊃ want(mary,like(x79,bill))
        -- ∀x76.person(x76) ⊃ want(mary,like(x76,bill))
        -- ∀x76.person(x76) ⊃ want(mary,like(x76,bill))
        -- ∀x73.person(x73) ⊃ want(mary,like(x73,bill))

eng13 = show2 (Pair mary (Pair wants (Pair to (Pair like someone))))
        <$> findAll (MARY ∙ WANTS ∙ TO ∙ LIKE ∙ SOMEONE ⊢ S)
        -- 3
        -- want(mary,∃x67.person(x67) ∧ like(mary,x67))
        -- ∃x86.person(x86) ∧ want(mary,like(mary,x86))
        -- ∃x83.person(x83) ∧ want(mary,like(mary,x83))

eng14 = show2 (Pair mary (Pair (Pair wants john) (Pair to (Pair like someone))))
        <$> findAll (MARY ∙ (WANTS ∙ JOHN) ∙ TO ∙ LIKE ∙ SOMEONE ⊢ S)
        -- 3
        -- want(mary,∃x71.person(x71) ∧ like(john,x71))
        -- ∃x90.person(x90) ∧ want(mary,like(john,x90))
        -- ∃x87.person(x87) ∧ want(mary,like(john,x87))

eng15 = show2 (Pair mary (Pair (Pair wants everyone) (Pair to (Pair like someone))))
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

eng16 = show2 (Pair mary (Pair says (Pair john (Pair likes bill))))
        <$> findAll (MARY ∙ SAYS ∙ (SDIA SReset (JOHN ∙ LIKES ∙ BILL)) ⊢ S)
        -- 1
        -- say(mary,like(john,bill))

eng17 = show2 (Pair mary (Pair says (Pair everyone (Pair likes bill))))
        <$> findAll (MARY ∙ SAYS ∙ (SDIA SReset (EVERYONE ∙ LIKES ∙ BILL)) ⊢ S)
        -- 1
        -- say(mary,∀x40.person(x40) ⊃ like(x40,bill))

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


type    JOHN     = NP
type    MARY     = NP
type    BILL     = NP
type    RUN      = IV                                     ; type    RUNS   = RUN
type    LIKE     = TV                                     ; type    LIKES  = LIKE
type    SERVE    = TV                                     ; type    SERVES = SERVE
type    WANT     = (IV :← INF) :& ((IV :← INF) :← NP)     ; type    WANTS  = WANT
type    LEAVE    = IV                                     ; type    LEAVES = LEAVE
type    SAY      = IV :← Dia Reset S                      ; type    SAYS   = SAY
type    THE      = DET
type    TO       = INF :← IV
type    SAME     = Q A NP'S NP'S
type    WAITER   = N
type    PERSON   = N
type    SOMEONE  = Q NP S S
type    EVERYONE = Q NP S S
pattern JOHN     = NP
pattern MARY     = NP
pattern BILL     = NP
pattern RUN      = IV                                     ; pattern RUNS   = RUN
pattern LIKE     = TV                                     ; pattern LIKES  = LIKE
pattern SERVE    = TV                                     ; pattern SERVES = SERVE
pattern WANT     = (IV :%← INF) :%& ((IV :%← INF) :%← NP) ; pattern WANTS  = WANT
pattern LEAVE    = IV                                     ; pattern LEAVES = LEAVE
pattern SAY      = IV :%← SDia SReset S                   ; pattern SAYS   = SAY
pattern THE      = DET
pattern TO       = INF :%← IV
pattern SAME     = Q A NP'S NP'S
pattern WAITER   = N
pattern PERSON   = N
pattern SOMEONE  = Q NP S S
pattern EVERYONE = Q NP S S


pattern Forall u = App (Con "∀") (Abs u)
pattern Exists u = App (Con "∃") (Abs u)
pattern x :∧ y = App (App (Con "∧") x) y
pattern x :⊃ y = App (App (Con "⊃") x) y
