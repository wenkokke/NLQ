% ---------------------------------------------------------------------
% Lambda term normalization
% ---------------------------------------------------------------------
% From Richard Moot's Grail code

reduce_sem(Term0,Term) :-
    reduce_sem1(Term0,Term1),
    !,
    reduce_sem(Term1,Term).

reduce_sem(Term,Term).

reduce_sem1(appl(lambda(X,T0),T1),T) :-
	replace_sem(T0,X,T1,T).

				
reduce_sem1(lambda(X,appl(F,X)),F):-
     \+ subterm(F,X).

reduce_sem1(fst(pair(T,_)),T).
reduce_sem1(snd(pair(_,T)),T).
reduce_sem1(pair(fst(T),snd(T)),T).

% = recursive case

reduce_sem1(T,U) :-
     T =.. [F|Ts],
     reduce_list(Ts,Us),
     U =.. [F|Us].

subterm(X,X) :- !.
subterm(X,Y) :-
     functor(X,_,N),
     subterm(N,X,Y).

subterm(N0,X,Y) :-
     N0>0,
     arg(N0,X,A),
     subterm(A,Y).

subterm(N0,X,Y) :-
     N0>0,
     N is N0-1,
     subterm(N,X,Y).

reduce_list([T|Ts],[U|Ts]) :-
     reduce_sem1(T,U).
reduce_list([T|Ts],[T|Us]) :-
     reduce_list(Ts,Us).


replace_sem(X,X,Y,Y) :- !.
replace_sem(U,X,Y,V) :-
     functor(U,F,N),
     functor(V,F,N),
     replace_sem(N,U,X,Y,V).

replace_sem(0,_,_,_,_) :- !.
replace_sem(N0,U,X,Y,V) :-
     N0>0,
     N is N0-1,
     arg(N0,U,A),
     replace_sem(A,X,Y,B),
     arg(N0,V,B),
     replace_sem(N,U,X,Y,V).

% Latex

%% CPS variables

write_sem('$VAR'(N),_) :-
        !,
        V is N mod 3,
        I is N // 3,
        new_cps_var_name(V,Name),
        write(Name),write('_{'),write(I),
        write('}').

write_sem(cps_var('$VAR'(N)),_):-
        !,
        V is N mod 3,
        I is N // 3,
        sem_var_name(V,Name),
        write('\\widetilde{'),
        write(Name),write('}_{'),write(I),write('}').
        
write_sem(cps_covar('$VAR'(N)),_):-
        !,
        V is N mod 3,
        I is N // 3,
        sem_covar_name(V,Name),
        write('\\widetilde{'),
        write(Name),write('}_{'),write(I),write('}').

write_sem(cps_var(Atom),_):-
        atom(Atom),
        !,
        write('\\CBVlex{\\W{'),
		write_sem(Atom,_),
		write('}}').     

%% lambda-mu-comu

write_sem(var('$VAR'(N)):_/_,_):-
        !,
        V is N mod 3,
        I is N // 3,
        sem_var_name(V,Name),
        write(Name),write('_{'),write(I),
        write('}^{'),
%        write(Type),
        write('}').


write_sem(var('$VAR'(N)),_):-
        !,
        V is N mod 3,
        I is N // 3,
        sem_var_name(V,Name),
        write(Name),write('_{'),write(I),write('}').
        
write_sem(covar('$VAR'(N)):_/_,_):-
        !,
        V is N mod 3,
        I is N // 3,
        sem_covar_name(V,Name),
        write(Name),write('_{'),write(I),
        write('}^{'),
%        write(Type),
        write('}').

write_sem(covar('$VAR'(N)),_):-
        !,
        V is N mod 3,
        I is N // 3,
        sem_covar_name(V,Name),
        write(Name),write('_{'),write(I),write('}').
               
write_sem(var(Atom),_):-
        atom(Atom),
        !,
%        write('\\rule[-1ex]{0pt}{2ex}'),
		write_sem(Atom,_).
        
write_sem(covar(Atom),_):-
		atom(Atom),
        !,
		write_sem(Atom,_).

write_sem(lneg(T),_) :-
        !,
        write('{}^{0}\\left('),
        write_sem(T,1),
        write('\\right)').	  
write_sem(rneg(T),_) :-
        !,
        write('\\left('),
        write_sem(T,1),
        write('\\right)^{0}').	 
 
write_sem(ldneg(T),_) :-
        !,
        write('{}^{1}\\left('),
        write_sem(T,1),
        write('\\right)').	  
write_sem(rdneg(T),_) :-
        !,
        write('\\left('),
        write_sem(T,1),
        write('\\right)^{1}').	 
                                    
write_sem(rapp(K,M),_):-
        !,
        write('('),
        write_sem(K,1),
%        write(' \\mathbin{\\rtimes} '),
        write(' \\mathbin{\\slash} '),
        write_sem(M,1),
        write(')').
        
write_sem(lapp(M,K),_):-
        !,
        write('('),
        write_sem(M,1),
%        write(' \\mathbin{\\ltimes}  '),
        write(' \\mathbin{\\bs} '),
        write_sem(K,1),
        write(')').
 
write_sem(otimes(M,N),_):-
        !,
        write('('),
        write_sem(M,1),
%        write(' \\mathbin{\\ltimes}  '),
        write(' \\otimes '),
        write_sem(N,1),
        write(')').

write_sem(oplus(K,L),_):-
        !,
        write('('),
        write_sem(K,1),
%        write(' \\mathbin{\\ltimes}  '),
        write(' \\oplus '),
        write_sem(L,1),
        write(')').
                      
write_sem(rcoapp(M,K),_):-
        !,
        write('('),
        write_sem(M,1),
%        write(' \\mathbin{\\Yright} '),
        write(' \\mathbin{\\oslash} '),
        write_sem(K,1),
        write(')').
        
write_sem(lcoapp(K,M),_):-
        !,
        write('('),
        write_sem(K,1),
%        write(' \\mathbin{\\Yleft} '),
        write(' \\mathbin{\\obslash} '),
        write_sem(M,1),
        write(')').
        
write_sem(bullet(M,K),_):-
        !,
        write('\\langle\\ '),
        write_sem(M,1),
        write(' \\mid '),
        write_sem(K,1),
        write('\\ \\rangle'). 

/* write_sem(bullet(M,K),_):-
        !,
        write('\\dfrac{\\rule[-1ex]{0pt}{2ex}'),
        write_sem(K,1),
        write('}{\\rule[-1ex]{0pt}{2ex}'),
        write_sem(M,1),
        write('}').       */ 
        
write_sem(mu(Alpha,S),N):-
        !,
        write_bo(N),
        write('\\mu '),
        write_sem(Alpha,1),
        write('.'),
        binding(S,mu(Alpha,S),NV),
        write_sem(S,NV),
        write_bc(N).


write_sem(mu_over(Alpha,X,S),N):-
        !,
        write_bo(N),
        write('\\lambda ('),
        write_sem(Alpha,1),
        write(','),
        write_sem(X,1),
        write(').'),
        binding(S,mu(Alpha,S),NV),
        write_sem(S,NV),
        write_bc(N).

write_sem(mu_under(X,Alpha,S),N):-
        !,
        write_bo(N),
        write('\\lambda ('),
        write_sem(X,1),
        write(','),
        write_sem(Alpha,1),
        write(').'),
        binding(S,mu(Alpha,S),NV),
        write_sem(S,NV),
        write_bc(N).

write_sem(comu(X,S),N):-
        !,
        write_bo(N),
        write('\\comu '),
        write_sem(X,1),
        write('.'),
        binding(S,comu(X,S),NV),
        write_sem(S,NV),
        write_bc(N).

write_sem(comu_lneg(X,S),N) :-
		!,
        write_bo(N),
        write('\\widetilde{\\lambda} {}^{0}('),
        write_sem(X,1),
        write(').'),
        binding(S,comu(X,S),NV),
        write_sem(S,NV),
        write_bc(N).		

write_sem(comu_rneg(X,S),N) :-
		!,
        write_bo(N),
        write('\\widetilde{\\lambda} ('),
        write_sem(X,1),
        write(')^{0}.'),
        binding(S,comu(X,S),NV),
        write_sem(S,NV),
        write_bc(N).	
  
write_sem(mu_ldneg(Alpha,S),N) :-
		!,
        write_bo(N),
        write('\\lambda {}^{1}('),
        write_sem(Alpha,1),
        write(').'),
        binding(S,mu(Alpha,S),NV),
        write_sem(S,NV),
        write_bc(N).		

write_sem(mu_rdneg(Alpha,S),N) :-
		!,
        write_bo(N),
        write('\\lambda ('),
        write_sem(X,1),
        write(')^{1}.'),
        binding(S,mu(Alpha,S),NV),
        write_sem(S,NV),
        write_bc(N).	
              
write_sem(comu_oslash(X,Alpha,S),N):-
        !,
        write_bo(N),
        write('\\widetilde{\\lambda} ('),
        write_sem(X,1),
        write(','),
        write_sem(Alpha,1),
        write(').'),
        binding(S,comu(X,S),NV),
        write_sem(S,NV),
        write_bc(N).
        
write_sem(comu_obslash(Alpha,X,S),N):-
        !,
        write_bo(N),
        write('\\widetilde{\\lambda} ('),
        write_sem(Alpha,1),
        write(','),
        write_sem(X,1),
        write(').'),
        binding(S,comu(X,S),NV),
        write_sem(S,NV),
        write_bc(N).


write_sem(Const,_) :-
		atom(Const),
		!,
        write('\\textsf{'),
        write(Const),
        write('}').

write_sem(lambda(X,V),N) :-
        !,
        write_bo(N),
        write('\\lambda '),
        write_sem(X,1),
        write('.'),
        binding(V,lambda(X,V),NV),
        write_sem(V,NV),
        write_bc(N).
        
write_sem(appl(X,Y),_) :-
        !,
        write('('),
        write_sem(X,1),
        write(' \\  '),
        write_sem(Y,1),
        write(')').

write_sem(pair(X,Y),_) :-
        !,
        write(' \\langle '),
        write_sem(X,1),
        write(' , '),
        write_sem(Y,1),
        write(' \\rangle ').

write_sem(fst(X),_) :-
        !,
        write(' \\pi^1'),
        binding(X,fst(X),NX),
        write_sem(X,NX).

write_sem(snd(X),_) :-
        !,
        write(' \\pi^2'),
        binding(X,snd(X),NX),
        write_sem(X,NX).
        
new_cps_var_name(0,k).
new_cps_var_name(1,h).
new_cps_var_name(2,u).

sem_var_name(0,x).
sem_var_name(1,y).
sem_var_name(2,z).

sem_covar_name(0,'\\alpha').
sem_covar_name(1,'\\beta').
sem_covar_name(2,'\\gamma').


write_bo(0) :- write('(').
write_bo(1).

write_bc(0) :- write(')').
write_bc(1).



binding(_,_,0).

bind1( _,T,T,M ,M,1) :- !.
bind1(=<,_,_,M0,M,N) :- (M >  M0 -> N = 0 ; N = 1).
bind1( <,_,_,M0,M,N) :- (M >= M0 -> N = 0 ; N = 1).

binds(dia(_,_),n,=<,20).
binds(box(_,_),n,=<,20).
binds(p(I,_,_),p(I,_,_),<,8) :- ignore_brackets(I),!.
binds(p(_,_,_),n,<,8).
binds(dl(_,_,_),n,<,4).
binds(dr(_,_,_),n,<,4).

binds(not(_),n,=<,20).
binds(dedia(_),n,=<,20).
binds(condia(_),n,=<,20).
binds(debox(_),n,=<,20).
binds(conbox(_),n,=<,20).
binds(quant(_,_,_),n,=<,12).
binds(lambda(_,_),n,=<,12).
binds(rlambda(_,_),n,=<,12).
binds(llambda(_,_),n,=<,12).
binds(rcolambda(_,_),n,=<,12).
binds(lcolambda(_,_),n,=<,12).
binds(mu(_,_),n,=<,12).
binds(comu(_,_),n,=<,12).
binds(bool(_,&,_),bool(_,&,_),<,8).
binds(bool(_,\/,_),bool(_,\/,_),<,8).
binds(bool(_,->,_),n,<,4).
binds(merge(_,_),merge(_,_),<,2).

