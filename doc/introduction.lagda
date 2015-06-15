``` hidden
module introduction where
```

# Introduction

- for the systems we introduce, we will not busy ourselves with
  rewrite rules, normalisation, etc.

- we will define translations of various systems into intuitionistic
  logic (or the simply-typed lambda calculus) either directly or
  through a continuation-passing style translation;

- all our logical fragments will remain propositional, and many will
  be fragments of non-commutative linear logic;

- we will translate our proofs in intuitionistic logic back into Agda,
  piggy-backing on the implementation to obtain evaluation;

- the intermediate translation to IL will guarantee that we do not use
  any constructions not available in IL in the translation of our
  systems;


# Overview

The general overview of the thesis is as follows:

  - What is a type-logical grammar?

      * What is a type theory?
      * Give an implementation of indexed lambda calculus.

  - What are substructural type theories?

      * Give an implementation of lambda calculus with explicit
      structure.

  - What is linear type theory?

      * Explain linear type theory.
      * Mention affine type theory, mention relevant type theory.
      * Give an implementation of linear lambda calculus.
      * Give a translation of linear lambda calculus into lambda
      calculus.

  - What is ordered type theory / the Lambek calculus?

      * Explain ordered type theory.
      * Mention associative type theory, mention commutative type
        theory.
      * Give a natural deduction implementation of the Lambek
        calculus.
      * Touch upon natural deduction versus sequent calculus, and cut
        elimination as normalisation.
      * Give a sequent calculus implementation of Lambek calculus.
      * Give the algebraic implementation due to Moortgat, and explain
        its advantages in terms of spurious ambiguity and proof
        search.

  - What is a multi-modal type-logical grammar?

      * What is the Lambek-Grishin calculus?

          + Explain general multi-modal type-logical grammars.
          + Give the algebraic Lambek-Grishin calculus.
          + Give a CPS translation of aLG.
          + Explain focusing.
          + Give the structural Lambek-Grishin calculus.
          + Give a CPS translation of sLG.
          + Give proof of equivalence between sLG and aLG.
          + Explain polarity.
          + Give the polarised Lambek-Grishin calculus.
          + Give a CPS translation of fLG.
          + Give proof of equivalence between fLG and sLG.

      * How can the Lambek-Grishin calculus be applied to linguistics?

          + Give analyses of sentences in linguistic data.

      * What is Moortgat's system for in-situ binding / $\text{NL}_{CL}$?

          + Give explanation of Moortgat's in-situ binding (1996).
          + Give implementation of $\text{NL}_{CL}$.
          + Explain limitations of $\text{NL}_{CL}$.
          + Give merge of $\text{NL}_{CL}$ ang Moorgat's work of licensing
            movement using diamonds.


<!--

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

*Once all these concepts are familiar, I will delve into a slightly
 deeper motivation of why this particular approach is important.*

-->
