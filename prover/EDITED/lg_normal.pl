:- [type2lex,lg_output,lg_lexicon].
:- dynamic atom_polarity/1.

:- make_lexicon.

atom_polarity(pos). % atom polarity can be changed with atom_pol/1.

% translating derivations

proof0(infer1(rightdown,Conclusion1,Premise),Term) --> % last step: activate
	[infer],
	un(rightdown),
	sequent(Conclusion),
	[from],
	proof(Premise,Term0),
	{activate0(Name,Conclusion,Conclusion1,Premise,Term0,Term)}.

activate0(rightdown,vdashright(_,lit(Out)),vdashright(In1,lit(Out)),P,Term0,mu(covar(Alpha),Term0)):-
	P=..[_,_,vdash(In1,covar(Alpha):lit(Out))|_].

proof(infer0(ax,vdashright(var(X):lit(A),lit(A))),var(X)) --> % axiom
	[infer],
	zero,
	[vdashright,lit(A),lit(A)],
	[from].

proof(infer0(coax,vdashleft(lit(A),covar(Alpha):lit(A))),covar(Alpha)) --> % coaxiom
	[infer],
	zero,
	[vdashleft,lit(A),lit(A)],
	[from].

proof(infer1(Name,vdash(In1,Out1),Premise),Term) --> % structural
	[infer],
	un(Name),
	{member(Name,[r,dr,gc,dgc,d_oslash_slash,d_oslash_backslash,d_obslash_slash,d_obslash_backslash])},
	sequent(vdash(In,Out)),
	[from],
	proof(Premise,Term),
	{rearrange(Name,In,Out,In1,Out1,Premise),
	label(In,In1),label(Out,Out1)}.

rearrange(r,_,str_over(_,_),S1,str_over(S3,S2),P):-
	P=..[_,_,vdash(str_otimes(S1,S2),S3)|_].
rearrange(r,_,str_under(_,_),S2,str_under(S1,S3),P):-
	P=..[_,_,vdash(str_otimes(S1,S2),S3)|_].
rearrange(r,str_otimes(_,_),_,str_otimes(S1,S2),S3,P):-
	P=..[_,_,vdash(S1,str_over(S3,S2))|_].
rearrange(r,str_otimes(_,_),_,str_otimes(S1,S2),S3,P):-
	P=..[_,_,vdash(S2,str_under(S1,S3))|_].

rearrange(dr,str_oslash(_,_),_,str_oslash(S1,S3),S2,P):-
	P=..[_,_,vdash(S1,str_oplus(S2,S3))|_].
rearrange(dr,str_obslash(_,_),_,str_obslash(S2,S1),S3,P):-
	P=..[_,_,vdash(S1,str_oplus(S2,S3))|_].
rearrange(dr,_,str_oplus(_,_),S1,str_oplus(S2,S3),P):-
	P=..[_,_,vdash(str_oslash(S1,S3),S2)|_].
rearrange(dr,_,str_oplus(_,_),S1,str_oplus(S2,S3),P):-
	P=..[_,_,vdash(str_obslash(S2,S1),S3)|_].

rearrange(d_oslash_slash,str_oslash(_,_),str_over(_,_),str_oslash(X,W),str_over(Z,Y),P):-
	P=..[_,_,vdash(str_otimes(X,Y),str_oplus(Z,W))|_].
rearrange(d_oslash_backslash,str_oslash(_,_),str_under(_,_),str_oslash(Y,W),str_under(X,Z),P):-
	P=..[_,_,vdash(str_otimes(X,Y),str_oplus(Z,W))|_].
rearrange(d_obslash_slash,str_obslash(_,_),str_over(_,_),str_obslash(Z,X),str_over(W,Y),P):-
	P=..[_,_,vdash(str_otimes(X,Y),str_oplus(Z,W))|_].
rearrange(d_obslash_backslash,str_obslash(_,_),str_under(_,_),str_obslash(Z,Y),str_under(X,W),P):-
	P=..[_,_,vdash(str_otimes(X,Y),str_oplus(Z,W))|_].

rearrange(gc,_,_,S2,lNeg(S1),P):-
	P=..[_,_,vdash(S1,rNeg(S2))|_].
rearrange(gc,_,_,S2,rNeg(S1),P):-
	P=..[_,_,vdash(S1,lNeg(S2))|_].
rearrange(dgc,_,_,ldNeg(S1),S2,P):-
	P=..[_,_,vdash(rdNeg(S2),S1)|_].
rearrange(dgc,_,_,rdNeg(S1),S2,P):-
	P=..[_,_,vdash(ldNeg(S2),S1)|_].

label(Str,Labeled):-
	Str=..[Op,S1],
	member(Op,[lNeg,rNeg,ldNeg,rdNeg]),
	!,
	Labeled=..[Op,L1],
	label(S1,L1).

label(Str,Labeled):-
	Str=..[Op,S1,S2],
	member(Op,[str_over,str_under,str_otimes,str_oslash,str_obslash,str_oplus,d_oslash_slash,d_oslash_backslash,d_obslash_slash,d_obslash_backslash]),
	!,
	Labeled=..[Op,L1,L2],
	label(S1,L1),
	label(S2,L2).

label(InType,var(_):InType).
label(OutType,covar(_):OutType).

proof(infer1(Name,Conclusion1,Premise),Term) --> % activate
	[infer],
	un(Name),
	{member(Name,[rightdown,leftdown])},
	sequent(Conclusion),
	[from],
	proof(Premise,Term0),
	{activate(Name,Conclusion,Conclusion1,Premise,Term0,Term)}.

activate(rightdown,vdashright(_,Out),vdashright(In1,Out),P,Term0,mu(covar(Alpha),Term0)):-
	pol(neg,Out),
	P=..[_,_,vdash(In1,covar(Alpha):Out)|_].
activate(leftdown,vdashleft(In,_),vdashleft(In,Out1),P,Term0,comu(var(X),Term0)):-
	pol(pos,In),
	P=..[_,_,vdash(var(X):In,Out1)|_].

proof(infer1(Name,Conclusion1,Premise),Term) --> % deactivate
	[infer],
	un(Name),
	{member(Name,[rightup,leftup])},
	sequent(Conclusion),
	[from],
	proof(Premise,Term0),
	{deactivate(Name,Conclusion,Conclusion1,Premise,Term0,Term)}.

deactivate(rightup,vdash(_,Out),vdash(In1,covar(Alpha):Out),P,Term0,bullet(Term0,covar(Alpha))):-
	P=..[F,Name,vdashright(In1,Out)|_],
	(pol(pos,Out);
	pol(neg,Out),
	F=infer1,
	member(Name,[slash_right,backslash_right,oplus_right,lneg_right,rneg_right])).


deactivate(leftup,vdash(In,_),vdash(var(X):In,Out1),P,Term0,bullet(var(X),Term0)):-
	P=..[F,Name,vdashleft(In,Out1)|_],
	(%In=lit(_); % a thinks somebody left
	pol(neg,In);
	pol(pos,In),
	F=infer1,
	member(Name,[oslash_left,obslash_left,otimes_left,ldneg_left,rdneg_left])).


proof(infer1(Name,Conclusion1,Premise),Term) --> % reversible logical
	[infer],
	un(Name),
	{member(Name,
		[slash_right,backslash_right,oplus_right,
		oslash_left,obslash_left,otimes_left,
		ldneg_left,rdneg_left,
		lneg_right,rneg_right])},
	sequent(Conclusion),
	[from],
	proof(Premise,Term0),
	{rewrite(Name,Conclusion,Conclusion1,Premise,Term0,Term)}.

rewrite(slash_right,vdashright(_,over(A,B)),vdashright(In,over(A,B)),P,Term0,mu_over(covar(Alpha),var(Y),Term0)):-
	P=..[_,_,vdash(In,str_over(covar(Alpha):A,var(Y):B))|_].
rewrite(backslash_right,vdashright(_,under(B,A)),vdashright(In,under(B,A)),P,Term0,mu_under(var(Y),covar(Alpha),Term0)):-
	P=..[_,_,vdash(In,str_under(var(Y):B,covar(Alpha):A))|_].
rewrite(oplus_right,vdashright(_,oplus(B,A)),vdashright(In,oplus(B,A)),P,Term0,mu_oplus(covar(Beta),covar(Alpha),Term0)):-
	P=..[_,_,vdash(In,str_oplus(covar(Beta):B,covar(Alpha):A))|_].
rewrite(rneg_right,vdashright(_,rneg(A)),vdashright(In,rneg(A)),P,Term0,comu_rneg(var(X),Term0)):-
	P=..[_,_,vdash(In,rNeg(var(X):A))|_].
rewrite(lneg_right,vdashright(_,lneg(A)),vdashright(In,lneg(A)),P,Term0,comu_lneg(var(X),Term0)):-
	P=..[_,_,vdash(In,lNeg(var(X):A))|_].

rewrite(oslash_left,vdashleft(oslash(A,B),_),vdashleft(oslash(A,B),Out),P,Term0,comu_oslash(var(X),covar(Beta),Term0)):-
	P=..[_,_,vdash(str_oslash(var(X):A,covar(Beta):B),Out)|_].
rewrite(obslash_left,vdashleft(obslash(B,A),_),vdashleft(obslash(B,A),Out),P,Term0,comu_obslash(covar(Beta),var(X),Term0)):-
	P=..[_,_,vdash(str_obslash(covar(Beta):B,var(X):A),Out)|_].
rewrite(otimes_left,vdashleft(otimes(B,A),_),vdashleft(otimes(B,A),Out),P,Term0,comu_otimes(var(Y),var(X),Term0)):-
	P=..[_,_,vdash(str_otimes(var(Y):B,var(X):A),Out)|_].
rewrite(rdneg_left,vdashleft(rdneg(A),_),vdashleft(rdneg(A),Out),P,Term0,mu_rdneg(covar(Alpha),Term0)):-
	P=..[_,_,vdash(rdNeg(covar(Alpha):A),Out)|_].
rewrite(ldneg_left,vdashleft(ldneg(A),_),vdashleft(ldneg(A),Out),P,Term0,mu_ldneg(covar(Alpha),Term0)):-
	P=..[_,_,vdash(ldNeg(covar(Alpha):A),Out)|_].

proof(infer1(Name,vdashleft(In1,Out1),Premise),Term) --> % mono neg left
	[infer],
	un(Name),
	{member(Name,[lneg_left,rneg_left])},
	sequent(vdashleft(In,Out)),
	[from],
	proof(Premise,Term0),
	{compose(Name,In,Out,In1,Out1,Premise,Term0,Term)}.

compose(lneg_left,lneg(A),_,lneg(A),lNeg(X),P,Term0,lneg(Term0)):-
	P=..[_,_,vdashright(X,A)|_].
compose(rneg_left,rneg(A),_,rneg(A),rNeg(X),P,Term0,rneg(Term0)):-
	P=..[_,_,vdashright(X,A)|_].

proof(infer1(Name,vdashright(In1,Out1),Premise),Term) --> % mono neg right
	[infer],
	un(Name),
	{member(Name,[ldneg_right,rdneg_right])},
	sequent(vdashright(In,Out)),
	[from],
	proof(Premise,Term0),
	{compose(Name,In,Out,In1,Out1,Premise,Term0,Term)}.

compose(ldneg_right,_,ldneg(A),ldNeg(X),ldneg(A),P,Term0,ldneg(Term0)):-
	P=..[_,_,vdashleft(A,X)|_].
compose(rdneg_right,_,rdneg(A),rdNeg(X),rdneg(A),P,Term0,rdneg(Term0)):-
	P=..[_,_,vdashleft(A,X)|_].

proof(infer2(Name,vdashleft(In,Out1),Premise1,Premise2),Term3) --> % mono left
	[infer],
	bin(Name),
	{member(Name,[slash_left,backslash_left,oplus_left])},
	sequent(vdashleft(In,Out)),
	[from],
	proof(Premise1,Term1),
	[and],
	proof(Premise2,Term2),
	{compose_term(Name,Term3,Term1,Term2),
	compose_structure(Out,Out1,Premise1,Premise2)}.

proof(infer2(Name,vdashright(In1,Out),Premise1,Premise2),Term3) --> % mono right
	[infer],
	bin(Name),
	{member(Name,[oslash_right,obslash_right,otimes_right])},
	sequent(vdashright(In,Out)),
	[from],
	proof(Premise1,Term1),
	[and],
	proof(Premise2,Term2),
	{compose_term(Name,Term3,Term1,Term2),
	compose_structure(In,In1,Premise1,Premise2)}.

compose_structure(str_over(_,_),str_over(S2,S1),P1,P2) :-
	!,
	P1=..[_,_,vdashright(S1,_)|_],
	P2=..[_,_,vdashleft(_,S2)|_].
compose_structure(str_under(_,_),str_under(S1,S2),P1,P2) :-
	!,
	P1=..[_,_,vdashright(S1,_)|_],
	P2=..[_,_,vdashleft(_,S2)|_].
compose_structure(str_oplus(_,_),str_oplus(S1,S2),P1,P2) :-
	!,
	P1=..[_,_,vdashleft(_,S1)|_],
	P2=..[_,_,vdashleft(_,S2)|_].

compose_structure(str_oslash(_,_),str_oslash(S1,S2),P1,P2) :-
	!,
	P1=..[_,_,vdashright(S1,_)|_],
	P2=..[_,_,vdashleft(_,S2)|_].
compose_structure(str_obslash(_,_),str_obslash(S2,S1),P1,P2) :-
	!,
	P1=..[_,_,vdashright(S1,_)|_],
	P2=..[_,_,vdashleft(_,S2)|_].
compose_structure(str_otimes(_,_),str_otimes(S1,S2),P1,P2) :-
	!,
	P1=..[_,_,vdashright(S1,_)|_],
	P2=..[_,_,vdashright(S2,_)|_].

compose_term(slash_left,rapp(K,M),M,K).
compose_term(backslash_left,lapp(M,K),M,K).
compose_term(oslash_right,rcoapp(M,K),M,K).
compose_term(obslash_right,lcoapp(K,M),M,K).
compose_term(oplus_left,oplus(K,L),K,L).
compose_term(otimes_right,otimes(M,N),M,N).

sequent(vdash(In,Out)) --> [vdash],in_structure(In),out_structure(Out).
sequent(vdashleft(In,Out)) --> [vdashleft],formula(In),out_structure(Out).
sequent(vdashright(In,Out)) --> [vdashright],in_structure(In),formula(Out).

zero --> [name('')].

un(rightdown) --> [name('\\rightharpoondown')].
un(leftdown) --> [name('\\leftharpoondown')].
un(rightup) --> [name('\\rightharpoonup')].
un(leftup) --> [name('\\leftharpoonup')].

un(dr) --> [name(dr)].
un(r) --> [name(r)].
un(gc) --> [name(gc)].
un(dgc) --> [name(dgc)].

un(d_oslash_slash) --> [name('d \\oslash \\slash')].
un(d_oslash_backslash) --> [name('d \\oslash \\backslash')].
un(d_obslash_slash) --> [name('d \\obslash \\slash')].
un(d_obslash_backslash) --> [name('d \\obslash \\backslash')].

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

formula(lit(Atom)) --> [lit(Atom)].
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

in_structure(Form) --> formula(Form).
in_structure(ldNeg(Str)) --> [ldNeg],out_structure(Str).
in_structure(rdNeg(Str)) --> [rdNeg],out_structure(Str).
in_structure(str_otimes(S1,S2)) --> [str_otimes],in_structure(S1),in_structure(S2).
in_structure(str_oslash(S1,S2)) --> [str_oslash],in_structure(S1),out_structure(S2).
in_structure(str_obslash(S1,S2)) --> [str_obslash],out_structure(S1),in_structure(S2).

out_structure(Form) --> formula(Form).
out_structure(lNeg(Str)) --> [lNeg],in_structure(Str).
out_structure(rNeg(Str)) --> [rNeg],in_structure(Str).
out_structure(str_oplus(S1,S2)) --> [str_oplus],out_structure(S1),out_structure(S2).
out_structure(str_over(S1,S2)) --> [str_slash],out_structure(S1),in_structure(S2).
out_structure(str_under(S1,S2)) --> [str_backslash],in_structure(S1),out_structure(S2).

% Normal proofs

pol(Pol,lit(_)) :- atom_polarity(Pol).

pol(pos,Form) :- Form=..[C|_],member(C,[otimes,oslash,obslash,rdneg,ldneg]).
pol(neg,Form) :- Form=..[C|_],member(C,[oplus,under,over,lneg,rneg]).

atom_pol(Pol) :- retractall(atom_polarity(_)),assert(atom_polarity(Pol)).

% CPS translation

cbv1(var(X),lambda(K,appl(K,cps_var(X)))).

cbv1(mu_under(var(X),covar(Beta),C),lambda(K,appl(K,lambda(cps_covar(Beta),lambda(cps_var(X),C1))))) :-
	cbv1(C,C1).

cbv1(mu_over(covar(Beta),var(X),C),lambda(K,appl(K,lambda(cps_covar(Beta),lambda(cps_var(X),C1))))) :-
	cbv1(C,C1).

cbv1(mu_ldneg(covar(Alpha),C),lambda(cps_covar(Alpha),C1)):-
	cbv1(C,C1).

cbv1(mu_rdneg(covar(Alpha),C),lambda(cps_covar(Alpha),C1)):-
	cbv1(C,C1).

cbv1(lneg(M),M1):-
	cbv1(M,M1).

cbv1(rneg(M),M1):-
	cbv1(M,M1).

cbv1(rcoapp(M,K),lambda(U,appl(U,lambda(H,appl(M1,appl(H,K1)))))):-
	cbv1(M,M1),
	cbv1(K,K1).

cbv1(lcoapp(K,M),lambda(U,appl(U,lambda(H,appl(M1,appl(H,K1)))))):-
	cbv1(M,M1),
	cbv1(K,K1).

cbv1(mu(covar(Beta),S),lambda(cps_covar(Beta),S1)):-
	cbv1(S,S1).


cbv1(covar(Alpha),cps_covar(Alpha)).

cbv1(comu_oslash(var(X),covar(Beta),C),lambda(K,appl(K,lambda(cps_covar(Beta),lambda(cps_var(X),C1))))):-
	cbv1(C,C1).

cbv1(comu_obslash(covar(Beta),var(X),C),lambda(K,appl(K,lambda(cps_covar(Beta),lambda(cps_var(X),C1))))):-
	cbv1(C,C1).

cbv1(comu_lneg(var(X),C),lambda(K,appl(K,lambda(cps_var(X),C1)))):-
	cbv1(C,C1).

cbv1(comu_rneg(var(X),C),lambda(K,appl(K,lambda(cps_var(X),C1)))):-
	cbv1(C,C1).

cbv1(ldneg(K),lambda(K0,appl(K0,K1))):-
	cbv1(K,K1).

cbv1(rdneg(K),lambda(K0,appl(K0,K1))):-
	cbv1(K,K1).

cbv1(lapp(M,K),lambda(U,appl(M1,appl(U,K1)))):-
	cbv1(M,M1),
	cbv1(K,K1).

cbv1(rapp(K,M),lambda(U,appl(M1,appl(U,K1)))):-
	cbv1(M,M1),
	cbv1(K,K1).

cbv1(comu(var(X),S),lambda(cps_var(X),S1)):-
	cbv1(S,S1).

cbv1(bullet(M,K),appl(M1,K1)):-	% bullet(Term,Context) is Prolog for <Term | Context>
	cbv1(M,M1),
	cbv1(K,K1).

% substituting lexical items

words(var(X):_,Term) --> [Word],{sub_term(var(Y),Term),X==Y,X=Word}.
words(str_otimes(A,B),Term) --> !,words(A,Term),words(B,Term).

lexsem(cps_var('$VAR'(N)),cps_var('$VAR'(N))) :- !.
lexsem(cps_var(Word),Term):-
	atom(Word),
	lex(Word,_,Term),
	!.
lexsem(lambda(Var,A),lambda(Var,A1)):-!,
	lexsem(A,A1).
lexsem(appl(A,B),appl(A1,B1)) :-!,
	lexsem(A,A1),lexsem(B,B1).
lexsem(A,A).

yield([],[]).
yield([H|T],T1) :- (H='(' ; H=')'),!,yield(T,T1).
yield([H|T],[H|T1]) :- yield(T,T1).

derivation_number(Atom,Number):-
	atom_codes(Atom,Codes),
	char2num(0,Codes,0,Number0),
	Number is Number0+1.

char2num(_,[],A,A).
char2num(P,[H|T],A,Num):-
	A0 is (H-97)*(26^P),
	NewA is A0+A,
	P1 is P+1,
	char2num(P1,T,NewA,Num).

% main predicate

test :-
	write('Input: '),nl,
	readln(In),
	write('Goal: '),nl,
	readln(G),
	concat_atom(In,' ',Input),
	concat_atom(G,' ',Goal),
	concat_atom(['./lg','"',Input,'"','"',Goal,'"'],' ',Command),
	concat_atom(['/Users/pepijn/Projects/LGprover/LGprover','lex.txt','"',Input,'"','"',Goal,'"','1> /dev/null'],
		' ',Derivations),
	shell(Derivations),
	shell(Command),
	yield(In,String),
	shell('./lgescape'),
	consult('lgproof'),
	typeset(String).

typeset(String) :-
	tell('eg.tex'),
	proof(K,P),
	(proof0(Proof,Term,P,[])
	->
	(Proof=..[_,_,vdashright(Product,_)|_],
	words(Product,Term,String,[]),
	cbv1(Term,Term1),
	numbervars(Term,0,N0),
	write('\\['),
	derivation_number(K,Num),
	write(Num),
	write('.\\quad'),
	write_sem(Term,1),
	write('\\]'),
	nl,
	N1 is N0+1,
	numbervars(Term1,N1,N),
	reduce_sem(Term1,Term2),
	write('\\['),
	write_sem(Term2,1),
	write('\\]'),
	nl,
	lexsem(Term2,Term3),
	M is N+1,
	numbervars(Term3,M,_),
	reduce_sem(Term3,Term4),
	write('\\['),
	write_sem(Term4,1),
	write('\\]'),
	nl,nl,
	write('\\bigskip'),
	nl,nl)
	),
%	;
%	write('\\[\\textrm{---}\\]'),nl,nl),
	fail.

typeset(_) :- told,
%		write('Open display.pdf for viewing the solutions'),nl,
	shell('pdflatex display &> /dev/null'),	% change to system-specific command
	write('Open display.pdf for viewing the solutions').
%	shell('ps aux | grep Preview.app | grep -v grep; if [ $? = 0 ]; then open display.pdf; fi').
