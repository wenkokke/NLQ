# Overview

  1. Categorial Grammar
  2. Substructural Logic
  3. The Base Logic
       - Sequent Calculus
       - The system R

         *Incl. isomorphism with Sequent Calculus*
       - The system RM

         *Incl. executable cut-elimination procedure & isomorphism with R*
       - Intermezzo: Linear Logic

         *Incl. translation to Agda.*
       - Derivational Semantics

         *Incl. translation of RM to LL and "direct derivation" of Agda term.*
       - Display Calculus

         *Incl. isomorphism with RM*
       - Polarity & Focusing

         *Excl. isomorphism with sLG*
  4. Extended Categorial Grammar
       - The Lambek-Grishin Calculus
           * The system RM
           * Display Calculus
           * Polarity & Focusing
           * Intermezzo: Continuation-Passing Style
           * Derivational Semantics
           * Syntactically Delimited Continuations
       - Multi-modal Lambek Calculus
           * Barker & Shan's $\text{NL}_{CL}$
           * Licensing units
  5. Lessons learned
       - Encoding logical systems

         *Discussion of considerations when encoding logical systems:
         abstraction versus readability; implicit versus explicit
         structural rules; structural rules and spurious ambiguity;
         extracting fragments.*

       - Relation to programming language theory
         *Discussion of the applicability of various lessons learned
         in sections 3 and 4 to the implementation programming
         languages.*
  6. Conclusion

<!--
# Overview

  - **What is a type-logical grammar?**

    First we will discuss what a categorial grammar is; then we will
    move into examples of extended categorial grammars.

  - **What is a categorial grammar?**

    Give definition of a categorial grammar, as an interface together
    with *some* structure. Discuss Lambek's program. Then talk about
    residuated lattices and residuated algebras.

  - **The non-associative Lambek calculus.**

    Discuss the sequent calculus axiomatisation for the
    non-associative Lambek calculus, for which a proof of
    cut-elimination was given by @lambek1961 and later extended to
    include the product by @kandulski1988.

    Discuss Lambek's alternative combinator calculus, featuring
    residuation instead of contexts. Discuss the advantages and
    disadvantages of this formalisation. Discuss cut-elimination for
    this formalisation, as given by @moortgat1999.

  - **Extended categorial grammars**

    Discuss the possibility to allow additional connectives in a
    categorial grammar.

    Discuss the Lambek-Grishin calculus, as an extension of the Lambek
    calculus. Discuss the axiomatisation of the Lambek-Grishin
    calculus building upon Belnap's Display Calculus. Discuss the
    axiomatisation of the Lambek-Grishin calculus which restricts the
    polarity in certain cases.
    (minor contribution)
    Discuss the extension which has a syntactic reset-*like* delimiter.

    Discuss $\text{NL}_{CL}$, Moortgat's modal analysis of in situ
    binding [-@moortgat1996] and
    (minor contribution)
    the fusion of the two systems.

Formally verifying your work is incredibly useful, not only for you but also for
your audience.



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
