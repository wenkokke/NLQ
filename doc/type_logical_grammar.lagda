``` hidden
module type_logical_grammar where
```

# Type-Logical Grammar

While the name 'type-logical grammar' goes back to @morrill1994, the
idea of type-logical grammars goes back to two papers written by
Lambek [-@lambek1958; -@lambek1961].

Type-logical grammars are substructural logics, generally fragments of
non-commutative linear logic, designed for reasoning about the
structure of natural language. In these type theories, the atomic
types correspond to syntactic categories, such as *noun*, *noun
phrase* or *sentence*. Judgements, then, correspond to
grammaticality. For instance, the judgement
$$\text{NP} , \; \text{NP} \to \text{S} \vdash \text{S}$$
could be taken to mean that from an $\text{NP}$ constituent and an
$\text{NP} \to \text{S}$ constituent, in that order, we can construct
a valid sentence.


## Applications in linguistics


The justification for this is simple: in general, the number of times
a word appears, and the order in which the words appear, are
important.
If we were to allow weakening or exchange, we could add arbitrary
words to a sentence or change the order of the words, without changing
the grammaticality or meaning of the sentence. For instance, "Mary
read a book" would mean the same thing as \*"Mary twelve read blue a
fly bicycle book" or \*"book Mary a read".
If we were to allow contraction, we could contract two words with the
same syntactic category (e.g. two adjectives) without affecting the
meaning  of the sentence. This means that, for example, "a large blue
book" would mean the same as "a blue book" or "a large book".
