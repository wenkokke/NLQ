# Introduction

In my thesis, I will make the following contributions. I will:

  - formalise the theory of several interesting type-logical grammars
    using the proof assistant Agda;

  - implement fast tools for proof search, so that one can easily use
    type-logical grammars to parse real data;

  - use these two tools to implement a sort of literate programming
    for type-logical grammars, where the claims that a given sentence
    is accepted by some grammar are checked while compiling the paper,
    and the claims are supplemented with explicit proofs.

*I will start this thesis by explaining in broad terms what I will be
 doing, and providing a brief motivation.*

The goal of my thesis is two-fold:
First, I will demonstrate a set of tools for researching type-logical
grammar formalisms. I will do this in the following way:

  - by formalising several interesting type-logical grammars in type
    theory, and showing that the expected properties hold for them;
  - by implementing tools for proof search, such that one can easily
    use the discussed systems to parse real data;

*Then I will explain how to read this thesis.*

  - *For readers with little background in type theory. I will have a
    section which explains what type theory is, what proof assistants
    aim to do, what Agda is specifically.*
  - *For readers with little background in linguistics, I will have a
    section which explains the linguistic data that I will be using
    in this thesis.*


## What is a type-logical grammar?

Type-logical grammars are substructural type theories, which are
designed for reasoning about the structure of natural language. In
these type theories, atomic types correspond to syntactic categories,
such as *noun*, *noun phrase* or *sentence*. Judgements, then,
correspond to grammaticality. For instance, the judgement
$$\text{NP} , \; \text{NP} \to \text{S} \vdash \text{S}$$
could be taken to mean that from an $\text{NP}$ constituent and an
$\text{NP} \to \text{S}$ constituent (in that order) we can construct
a valid sentence.

The fact that type-logical grammars are *substructural* means that the
type theories are lacking one or more structural rules
(i.e. contraction, weakening and exchange).
Discarding these rules can make the type theories *resource-sensitive*
(by discarding contraction and weakening) or *order-sensitive* (by
discarding exchange).
Usually, type-logical grammars will do both.
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

*Once all these concepts are familiar, I will delve into a slightly
 deeper motivation of why this particular approach is important.*
