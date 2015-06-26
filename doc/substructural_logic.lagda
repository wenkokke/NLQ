# Substructural logic

A substructural logic is a logic which lacks one or more of the
traditional structural rules (i.e. contraction, weakening and
exchange). Below we will discuss the various effects these structural
rules have on type systems, and how they affect our program of
categorial grammar.


## Linear logic

Discarding contraction and weakening makes logics *resource
sensitive* [@girard1987; @girard1995].

Recently, there has been a lot of interest in linear type theory,
where the linear properties of the type system are exploited to allow
explicit de-allocation, in-place re-use of memory, more efficient
garbage collection and safe concurrency
[see @abramsky1993; @turner1999; @igarashi2000; @plasmeijer2002; @bernardy2015].

### Weakening

If we were to allow weakening, we could add arbitrary words to a
sentence, without changing the grammaticality of the sentence.
For instance, "Mary read a book" would mean the same thing as \*"Mary
twelve read blue a fly bicycle book".


### Contraction

Contraction is a bit more subtle than weakening. If we were to allow
contraction, we could contract two words with the same syntactic
category (e.g. two adjectives) without affecting the meaning  of the
sentence. This means that, for example, "a large blue book" would mean
the same as "a blue book" or "a large book".



## Ordered logic

Discarding exchange makes logics *order sensitive*, hence ordered
logic.

Some work has been done in the field of ordered type theory, where the
order sensitivity of the calculus is used to achieve even more
efficient memory management, which is possible due to having an even
more fine-grained type system than linear logic [see @petersen2003].


### Commutativity

If we were to allow commutativity, we could arbitrarily change the
order of the words, without affecting the grammaticality of the
sentence.
For instance, "Mary read a book" would mean the same thing as "book
Mary a read".


### Associativity

The original system for categorial grammars formulated in @lambek1958
included associativity. This seemed to be a sound choice, as it
allowed the system to check the grammaticality of strings of
words, as opposed to binary trees. However, in allowing associativity,
one invariably allows some undesirable sentences to be accepted as
grammatical [see @moot2012, pp. 105-106].

One argument is that in the calculus *with* associativity, |(n ⇐ n) ⊗
(n ⇐ n) ⊢ n ⇐ n| is a theorem. Since the most natural type assignment
for adjectives and the verb "to be" are |n ⇐ n| and |(np ⇒ s) ⇐ (n ⇐
n)|, the following sentence becomes derivable:

\*"The Hulk is green incredible"


## Unit elements and empty sequences

Though the removal of unit elements is uncommon in linear and ordered
type theory, it is nonetheless essential for our program
[see @moot2012, pp. 33].

If we were to allow unit elements (or empty antecedents) |𝟙 ⊢ n ⇐ n|
would be a theorem. Joined with the fact that |(n ⇐ n) ⇐ (n ⇐ n)| is a
natural type for "very", we can see that we could supply the empty
sequence as the first argument for "very". This means that the
following noun phrase becomes derivable:

\*"a very book"
