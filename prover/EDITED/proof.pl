%proof(a,[infer,name('\\rightharpoondown'),vdashright,ldneg,rdneg,np,np,from,infer,name('\\leftharpoonup'),vdash,ldneg,rdneg,np,np,from,infer,name('\\ldneg{.} L'),vdashleft,ldneg,rdneg,np,np,from,infer,name('dgc'),vdash,ldNeg,rdneg,np,np,from,infer,name('\\rightharpoonup'),vdash,rdNeg,np,rdneg,np,from,infer,name('\\rdneg{.} R'),vdashright,rdNeg,np,rdneg,np,from,infer,name(''),vdashleft,np,np,from]).


proof(infer0(Seq)) --> [infer],zero,sequent(Seq),[from].

proof(infer1(Name,Conclusion,Premise)) --> [infer],un(Name),sequent(Conclusion),[from],proof(Premise).

proof(infer2(Name,Conclusion,Premise1,Premise2)) --> [infer],bin(Name),sequent(Conclusion),[from],proof(Premise1),[and],proof(Premise2).

sequent(vdash(In,Out)) --> [vdash],structure(In),structure(Out).
sequent(vdashleft(In,Out)) --> [vdashleft],formula(In),structure(Out).
sequent(vdashright(In,Out)) --> [vdashright],structure(In),formula(Out).

zero --> [name('')].

un(rightdown) --> [name('\\rightharpoondown')].
un(leftdown) --> [name('\\leftharpoondown')].
un(rightup) --> [name('\\rightharpoonup')].
un(leftup) --> [name('\\leftharpoonup')].
un(dr) --> [name(dr)].
un(r) --> [name(r)].
un(gc) --> [name(gc)].
un(dgc) --> [name(dgc)].
un(ldneg_left) --> [name('\\ldneg{.} L')].
un(ldneg_right) --> [name('\\ldneg{.} R')].
un(rdneg_left) --> [name('\\rdneg{.} L')].
un(rdneg_right) --> [name('\\rdneg{.} R')].
un(lneg_left) --> [name('\\lneg{.} L')].
un(lneg_right) --> [name('\\lneg{.} R')].
un(rneg_left) --> [name('\\rneg{.} L')].
un(rneg_right) --> [name('\\rneg{.} R')].
un(slash_right) --> [name('\\slash R')].
un(backslash_right) --> [name('\\backslash R')].
un(oslash_left) --> [name('\\oslash L')].
un(obslash_left) --> [name('\\obslash L')].
un(oplus_right) --> [name('\\oplus R')].
un(otimes_left) --> [name('\\otimes L')].

bin(slash_left) --> [name('\\slash L')].
bin(backslash_left) --> [name('\\backslash L')].
bin(oslash_right) --> [name('\\oslash R')].
bin(obslash_right) --> [name('\\obslash R')].
bin(oplus_left) --> [name('\\oplus L')].
bin(otimes_right) --> [name('\\otimes R')].

formula(Atom) --> [lit(Atom)].
formula(Term) --> con1(Con1),formula(Form),{Term=..[Con1,Form]}.
formula(Term) --> con2(Con2),formula(Form1),formula(Form2),{Term=..[Con2,Form1,Form2]}.

con1(lneg) --> [lneg].
con1(rneg) --> [rneg].
con1(ldneg) --> [ldneg].
con1(rdneg) --> [rdneg].

con2(over) --> [slash].
con2(under) --> [backslash].
con2(otimes) --> [otimes].
con2(oslash) --> [oslash].
con2(obslash) --> [obslash].
con2(oplus) --> [oplus].

structure(Form) --> formula(Form).
structure(Term) --> str_con1(Con1),structure(Str),{Term=..[Con1,Str]}.
structure(Term) --> str_con2(Con2),structure(S1),structure(S2),{Term=..[Con2,S1,S2]}.

str_con1(str_lneg) --> [lNeg].
str_con1(str_rneg) --> [rNeg].
str_con1(str_ldneg) --> [ldNeg].
str_con1(str_rdneg) --> [rdNeg].

str_con2(str_over) --> [str_slash].
str_con2(str_under) --> [str_backslash].
str_con2(str_otimes) --> [str_otimes].
str_con2(str_oslash) --> [str_oslash].
str_con2(str_obslash) --> [str_obslash].
str_con2(str_oplus) --> [str_oplus].

reserved(A) :- member(A,[lneg,rned,ldneg,rdneg,slash,backslash,otimes,oslash,obslash,oplus]).
