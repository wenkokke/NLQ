lex(miyakowa,top,miyako).
lex(hiromiga,nom,hiromi).
lex(nanio,obslash(oslash(q,wh),acc),whacc).
lex(kaita,under(acc,under(nom,s)),wrote).
lex(to,under(s,ss),that).
lex(sinzita,under(ss,under(top,s)),believed).

lex(unicorn,n,unicorn).
lex(teacher,n,teacher).
lex(molly,np,molly).
lex(alice,np,alice).

lex(kity,oslash(i,obslash(np,i)), kity).
lex(kata,oslash(ep,obslash(np,ep)), kata).
lex(smiles,under(np,s),smiles).

lex(s,under(np,over(np,n)),gen).

lex(every,over(np,n),
	lambda(Q,lambda(P,appl('$\\forall$',lambda(X,appl(appl('$\\Rightarrow$',appl(P,X)),appl(Q,X))))))).
lex(some,over(np,n),
	lambda(Q,lambda(P,appl('$\\exists$',lambda(X,appl(appl('$\\wedge$',appl(P,X)),appl(Q,X))))))).
%lex(someone,ldneg(rdneg(np)),
%	'$\\exists$').
lex(everyone,ldneg(rdneg(np)),
	'$\\forall$').
lex(somebody,over(s,under(np,s)),
	lambda(C,lambda(V,appl(C,appl('$\\exists$',appl(V,lambda(Z,Z))))))).
lex(everything,under(over(s,np),s),
	lambda(C,lambda(V,appl(C,appl('$\\forall$',appl(V,lambda(Z,Z))))))).
lex(left,under(np,s),
	lambda(C,lambda(X,appl(C,appl(left,X))))).
lex(teases,over(under(np,s),np),
	lambda(VP,lambda(Y,appl(VP,lambda(C,lambda(X,appl(C,appl(appl(teases,Y),X)))))))).
lex(likes,over(ldneg(under(np,rdneg(s))),np),
	likes).
lex(thinks,over(under(np,s),s),
	lambda(VP,lambda(S,appl(VP,lambda(C,lambda(X,appl(C,appl(appl(thinks,S),X)))))))).
lex(claims,over(under(np,s),lneg(rneg(s))),
	lambda(VP,lambda(QS,appl(VP,lambda(C,lambda(X,appl(C,appl(appl(claims,QS),X)))))))).
lex(pictureof,over(n,lneg(rneg(np))),
	lambda(Q1,lambda(Q2,appl(Q1,lambda(X,appl(Q2,lambda(Y,appl(appl(pic,Y),X)))))))).
	
%lex(somebody,obslash(oslash(s,s),np),
%	lambda(Q,appl('$\\exists$',appl(Q,lambda(U,appl(U,lambda(Z,Z))))))).
%	lambda(Q,appl(appl(Q,lambda(U,appl(U,lambda(C,lambda(V,appl(C,appl(past,V))))))),'$\\exists$')) ).
lex(everybody,obslash(oslash(s,s),ldneg(rdneg(np))),
%	lambda(Q,appl('$\\forall$',appl(Q,lambda(U,appl(U,lambda(Z,Z))))))).
	lambda(Q,appl(appl(Q,lambda(U,appl(U,lambda(Z,Z)))),'$\\forall$')) ).
		
lex(dmnd,ldneg(rdneg(over(n,n))),
%	dmnd).
	lambda(K,appl(K,lambda(Q,lambda(P,appl(Q,lambda(X,appl(appl('$\\wedge$',appl(P,X)),appl(dmnd,X))))))))).
lex(strange,ldneg(rdneg(over(n,n))),
	lambda(K,appl(K,lambda(Q,lambda(P,appl(appl('$\\wedge$',appl(Q,P)),appl(spattstupid,(appl(Q,P))))))))).
lex(weird,over(ldneg(rdneg(n)),n),
	lambda(Q,lambda(P,appl(appl('$\\wedge$',appl(Q,lambda(K,appl(K,P)))),appl(speakeratt,appl(Q,lambda(K,appl(K,P)))))))).

lex(nice,over(n,n),nice).
lex(old,over(n,n),old).
lex(rel,obslash(oslash(s,under(n,n)),np),rel).

% a^nb^nc^n

%lex(a,a,a).
%lex(c,c,c).
%lex(b0,under(a,obslash(oslash(t,over(s,c)),oslash(i,obslash(t,i)))),b).
%lex(b1,under(oslash(i,obslash(t,i)),under(a,obslash(oslash(t,over(t,c)),oslash(i,obslash(t,i))))),b).

% MIX

lex(a,obslash(a,s),a).
lex(c,oslash(over(s,s),c),c).
lex(b,oslash(over(s,s),obslash(s,obslash(a,oslash(s,c)))),b).

lex(suspects,over(under(np,s),over(s,under(s,s))),suspects).
lex(somesome,obslash(oslash(s,s),np),somesome).
lex(cheats,under(np,s),cheats).


%