make_lexicon :-
	tell('lex.txt'),
	lex(Word,Type,_),
	write(Word),
	write(' :: '),
	type2lex(Type,L,[]),
	string_to_list(TypeString,L),
	write(TypeString),
	write('.'),
	nl,
	fail.

make_lexicon :- told,
	shell('cp lex.txt ~/Projects/LG/Jeroen/LGprover2/').

type2lex(Type) --> 
	{Type=..[F,A]},
	"(",
	pre1(F),
	blex(A),
	")".

type2lex(Type) --> 
	{Type=..[F,A]},
	"(",
	blex(A),
	post1(F),
	")".
		
type2lex(Type) --> 
	{Type=..[F,A,B]},
	"(",
	type2lex(A),
	binary(F),
	type2lex(B),
	")".
	
type2lex(Atom,L0,L1) :- atom(Atom),atom_to_chars(Atom,L0,L1).

blex(A) --> {atom(A)},!,"(",type2lex(A),")".
blex(A) --> type2lex(A).

pre1(lneg) --> "0".
pre1(ldneg) --> "1".
post1(rneg) --> "0".
post1(rdneg) --> "1".

binary(over) --> " / ".
binary(under) --> " \\ ".
binary(otimes) --> " (*) ".
binary(oslash) --> " (/) ".
binary(obslash) --> " (\\) ".
binary(oplus) --> " (+) ".