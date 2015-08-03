# Motivation

This thesis started out as an attempt to understand type-logical
grammars by verifying them in a proof assistant. Whereas the original
framework of categorial grammars [@lambek1958; @lambek1961] is rather
easy to understand, the systems at the cutting edge are much more
involved, and use more recent ideas such as continuation-passing style
translations, delimited continuations, display calculus, focused proof
search and polarisation.
My original idea was to create a series of verified grammars which
would gradually add these features into Lambek's categorial grammars,
while showing that the systems remain equivalent.
I believed then, and still do, that such verifications could be a
useful educational tool, as students would be able to fire up their
proof assistant, and play around with the grammar systems in an
interactive session.

In the course of doing research for this thesis, however, something
happened which changed the mission statement as given above much more
ambitious.
It may have been because when I started, I had very little training in
formal logic, but I found that many papers describing type-logical
grammars, logics or type theories were unnecessarily obtuse. Often the
authors left slight ambiguities in the formulation of their system,
which one did not notice while reading the paper, but were fatal
when trying to formalise the it. Other times, entire sections of
proofs would be missing, or the given proofs were simply wrong.
In the cases where the author did provide a verification, these were
often undocumented, unreadable and out of sync with the paper.
That is to say: while the code was often 'documented' in the sense
that it accompanied a paper, there were no or only few hints with
regards to which section of the code corresponded to which section of
the paper; in addition, the code often only verified a small section
of the paper, and often an outdated version of the theory.
Lastly, there is the problem of disparate technologies when it comes
to formatting: while research papers are almost always typeset in
\LaTeX, people often still write their code in ASCII, and make little
use of the flexibility their programming language has to offer. This
often leads to formulas such as `A × B → C` being written in the code
as something as unsightly as `Formula(IMPLIES, Formula(PRODUCT, "A",
"B"), "C")`. This is what I mean with 'unreadable'.

For this thesis, I decided on the following contributions:

 1. In order to try and remedy the gap between research papers and
    verified theory as described above, and minimise the chance for
    human error, this thesis will be written in literate code. This
    means that *all* theorems will be presented in the form of typeset
    code, which is directly present in the source files and is
    type-checked when compiling the thesis. I will report on my
    experiences doing this in section \ref{lessons-learned}.

 2. In order to satisfy my curiosity, and hopefully provide the reader
    with an enlightening formalisation of categorial grammars, I will
    provide a series of verifications of various forms of the
    non-associative Lambek calculus, which forms the basis of all
    extended categorial grammars, and most type-logical grammars. My
    aim is to slowly incorporate the various changes which have been
    made over the past decade, and motivate them in sections
    \ref{non-associative-lambek-calculus} and \ref{display-calculus}.

 3. In order to give an example of what a short literate paper would
    look like, I will present, in three brief sections, three extended
    categorial grammars (TODO add references).

 4. And lastly, in my quest to formalise as much as possible in
    type-logical grammar papers, I have implemented a small library
    which allows the user---given a verification of their system---to
    add verified claims of grammaticality, ungrammaticality and
    derived interpretation. This lead to a definition of what a
    type-logical grammar has to be, minimally, in order to be
    useful. It is with this small library that we will start in
    section \ref{type-logical-grammar}.
