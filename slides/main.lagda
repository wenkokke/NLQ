\documentclass[12pt,t]{beamer}

%include agda.fmt
%if False
\usepackage{bbm}%
\let\spec\code%
\let\endspec\endcode%
%endif
\include{preamble}

\begin{document}

\begin{frame}
  \frametitle{An abstract NLP pipeline}
  \centering\vfill
  \only<1>{%
    \begin{minipage}{0.3\textwidth}%
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
    \begin{minipage}{0.6\textwidth}%
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
  }
  \only<2>{%
    Mary:NP [see:TV.PAST fox:NP.PL]\\
    $\downarrow$\\
    \framebox{Categorial Grammar}\\
    $\downarrow$\\
    $∃ X. X ⊆ \mathbf{fox} ∧ \mathbf{past}(\mathbf{see}(\text{mary},X))$\\
  }
  \only<3>{%
    Mary:NP [saw:TV foxes:NP]\\
    $\downarrow$\\
    \framebox{Categorial Grammar}\\
    $\downarrow$\\
    $∃ X. X ⊆ \mathbf{fox} ∧ \mathbf{saw}(\text{mary},X)$\\
  }
  \only<4>{%
    Mary:NP [saw:TV foxes:NP]\\
    $\downarrow$\\
    \framebox{Categorial Grammar}\\
    $\downarrow$\\
    $\mathbf{saw}(\text{mary},\text{foxes})$\\
  }
  \note{%
    \begin{itemize}
    \item
      categorial grammars live in the `semantics' function of an NLP
      pipeline;
    \item
      so technically our inputs are trees annotated with type information,
      but since we're lazy we often pretend to forget about this, and just
      do the morphological analysis ad-hoc or not at all;
    \item
      and sometimes you only have an hour, so you'd like to forget how
      complicated plurals are for a second;
    \end{itemize}
  }
\end{frame}


\begin{frame}
  \frametitle{Principle of Compositionality}
  \centering\vfill
  \begin{quote}
  The meaning of a complex expression is determined by the meanings of
  its constituent expressions and the rules used to combine them.\\
  \hfill---Gottlob Frege
  \end{quote}
  \note{%
    \begin{itemize}
    \item
      while this is probably not something Frege literally said or
      wrote down at some point, he is frequently credited with the
      first modern formalisation of this ideal;
    \item
      in linguistics, there is the strong belief that natural language
      obeys this principle;
    \item
      it just so happens that there is a large body of work on
      composing expressions: functional programming!
    \end{itemize}
  }
\end{frame}

\begin{frame}
  \frametitle{Let's apply functional programming!}
  \centering\vfill
  $$mary : NP, \; saw : NP → NP → S, \; foxes : NP ⊢ S$$\\
  \vspace{\baselineskip}%
  \onslide<2-3>{
    \large
    Computer, tell me what this means!
  }
  \onslide<3>{%
    \begin{align*}
      \mathbf{saw}(mary,foxes)\\
      \mathbf{saw}(foxes,mary)\\
      \mathbf{saw}(mary,mary)\\
      \mathbf{saw}(foxes,foxes)\\
    \end{align*}
  }
\note{%
  \begin{itemize}
  \item
    we can apply functional programming here!
  \item
    let's encode our sentence as a context (a list of the available
    terms) and ask the computer what terms of the type `S' we can
    build from this context;
  \item
    this is all propositional logic i.e. simply-typed lambda calculus,
    so computing all possible terms is super decidable!
  \item
    well, the right interpretation is in there... so let's not give
    up, right?
  \end{itemize}
}
\end{frame}

\begin{frame}
  \frametitle{Let's apply \textit{some of} functional programming!}

  \only<1-2>{%
    \vfill

    The problems:
    \begin{align*}
      &\mathbf{saw}(foxes,mary)  &←&\;\text{We cannot enforce order}\\
      &\mathbf{saw}(mary,mary)   &←&\;\text{We can use $mary$ twice}\\
      &\mathbf{saw}(foxes,foxes) &←&\;\text{We can forget about $mary$}\\
    \end{align*}

    \onslide<2>{%
      The culprits:
      \begin{center}
        \begin{minipage}{.3\textwidth}
          \begin{prooftree}
            \AX$\Gamma , B , A , \Delta \fCenter C$
            \LeftLabel{E}
            \UI$\Gamma , A , B , \Delta \fCenter C$
          \end{prooftree}
        \end{minipage}
        \begin{minipage}{.28\textwidth}
          \begin{prooftree}
            \AX$A , \Gamma \fCenter B$
            \LeftLabel{C}
            \UI$A , A , \Gamma \fCenter B$
          \end{prooftree}
        \end{minipage}
        \begin{minipage}{.245\textwidth}
          \begin{prooftree}
            \AX$\Gamma \fCenter B$
            \LeftLabel{W}
            \UI$A , \Gamma \fCenter B$
          \end{prooftree}
        \end{minipage}
      \end{center}
    }
  }
  \only<3-4>{%
    \centering\vfill
    $$mary : NP, \; saw : NP → NP → S, \; foxes : NP ⊢ S$$\\
    \vspace{\baselineskip}%
    \onslide<4>{%
      Computer, show me what this means!\\
      \begin{align*}
        \vphantom{\mathbf{saw}(mary,foxes)}\\
        \vphantom{\mathbf{saw}(foxes,mary)}\\
        \vphantom{\mathbf{saw}(mary,mary)}\\
        \vphantom{\mathbf{saw}(foxes,foxes)}\\
      \end{align*}
    }
  }
  \only<5-7>{%
    \centering\vfill
    Problem with function application:\\
    \vspace{2\baselineskip}%
    \begin{minipage}{.45\textwidth}
      \begin{prooftree}
        \AX$\Gamma [ B ] \fCenter C$
        \AX$\Delta \fCenter A$
        \LeftLabel{→L}
        \BI$\Gamma [ \Delta, A → B ] \fCenter C$
      \end{prooftree}
    \end{minipage}
    \onslide<6-7>{%
      \begin{minipage}{.45\textwidth}
      \begin{prooftree}
        \AX$\Gamma [ B ] \fCenter C$
        \AX$\Delta \fCenter A$
        \LeftLabel{←L}
        \BI$\Gamma [ B ← A, \Delta ] \fCenter C$
      \end{prooftree}
    \end{minipage}
    \vspace{\baselineskip}%
    }
    \onslide<7>{%
      \begin{minipage}{.45\textwidth}
        \begin{prooftree}
          \AX$A, \Gamma \fCenter B$
          \LeftLabel{→R}
          \UI$\Gamma \fCenter A → B$
        \end{prooftree}
      \end{minipage}
      \begin{minipage}{.45\textwidth}
        \begin{prooftree}
          \AX$\Gamma, A \fCenter B$
          \LeftLabel{←R}
          \UI$\Gamma \fCenter B ← A$
        \end{prooftree}
      \end{minipage}
      \vspace{\baselineskip}%
      \begin{prooftree}
        \AXC{}
        \LeftLabel{AX}
        \UIC{$A \fCenter A$}
      \end{prooftree}
    }
    \vfill
  }
  \only<8-9>{%
    \centering\vfill
    $$mary : NP, \; saw : (NP → S) ← NP, \; foxes : NP ⊢ S$$\\
    \vspace{\baselineskip}%
    \onslide<9>{%
      Computer, show me what this means!\\
      \begin{align*}
        \mathbf{saw}(mary,foxes)\\
        \vphantom{\mathbf{saw}(foxes,mary)}\\
        \vphantom{\mathbf{saw}(mary,mary)}\\
        \vphantom{\mathbf{saw}(foxes,foxes)}\\
      \end{align*}
    }
  }
\end{frame}

\begin{frame}
  \frametitle{Joachim Lambek (1922--2014)}
  \centering
  \includegraphics[height=\paperheight]{Joachim_Lambek.jpg}
\end{frame}

\begin{frame}

\end{frame}

\end{document}
