# Introduction

Type-logical grammar is the field on the intersection of type-theory
and logic on the one hand, and linguistics on the other. An attempt is
made to apply the lessons from artificial languages to the natural
ones. But where are these lessons best applied? Consider an abstract
pipeline for natural language understanding:

\begin{center}
  \begin{minipage}{0.3\textwidth}
    \centering
    \framebox{Morphological}\\
    $\downarrow$\\
    \framebox{Lexical}\\
    $\downarrow$\\
    \framebox{Syntactic}\\
    $\downarrow$\\
    \framebox{Semantic}\\
    $\downarrow$\\
    \framebox{Pragmatic}\\
  \end{minipage}
  \begin{minipage}{0.6\textwidth}
    \centering
    ``Mary saw foxes.''\\
    $\downarrow$\\
    Mary see.PAST fox.PL\\
    $\downarrow$\\
    Mary:NP see:TV.PAST fox:NP.PL\\
    $\downarrow$\\
    Mary:NP [see:TV.PAST fox:NP.PL]\\
    $\downarrow$\\
    $∃ X. X ⊆ \mathbf{fox} ∧ \mathbf{past}(\mathbf{see}(\text{Mary},X))$\\
    $\downarrow$\\
    \ldots\\
  \end{minipage}
\end{center}

To the left we see the several phases that work on a sentence, to
the right we see their inputs and outputs:

  - in the morphological phase, words are lemmatised, and the removed
    morphemes are inserted back into the sentence as e.g. PAST or PL;

  - in the lexical phase, the lemmas are matched against a lexicon,
    and annotated with their part-of-speech tags or categories;

  - in the syntactic phase, a parse tree is constructed;

  - in the semantic phase, the words are interpreted as logical
    expression, and the tree of logical expressions is then composed
    into a single logical expression representing the sentence
    meaning;

  - and lastly, in the pragmatic phase, the meaning of the sentence is
    completed by and integrated with the meanings of preceding
    sentences and other contextual information.

There is some debate as to which of these roles type-logical grammar
is supposed to fulfil, but generally, researchers focus on the
semantic phase---and no surprise, for this is where type-logical
grammar shines! The problem is essentially to take a tree of
expression and compose them into a single expression. The complexity
arises from the fact that not all expressions of natural language are
directly compositional---many expressions have side effects, or odd
scoping and binding behaviours. For instance,






This means that `type-logical grammar' can generally be though of as
the following function:

\begin{center}
  Mary:NP [see:TV.PAST fox:NP.PL]\\
  $\downarrow$\\
  \framebox{Type-Logical Grammar}\\
  $\downarrow$\\
  $∃ X. X ⊆ \mathbf{fox} ∧ \mathbf{past}(\mathbf{see}(\text{mary},X))$\\
\end{center}



\begin{center}
  Mary:NP [saw:TV foxes:NP]\\
  $\downarrow$\\
  \framebox{Type-Logical Grammar}\\
  $\downarrow$\\
  $∃ X. X ⊆ \mathbf{fox} ∧ \mathbf{saw}(\text{mary},X)$\\
\end{center}
