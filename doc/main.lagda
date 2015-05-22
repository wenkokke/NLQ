\documentclass{article}

%include agda.fmt
\include{preamble}%

% -------------------------- %
% 0 - Introduction
% 1 - Motivation
% -------------------------- %
% 2 - Agda Tutorial
% 3 - Linguistic Data
%     * Scope ambiguity
%     * Binding and crossover (?)
%     * Scope-taking adjectives
%     * Anaphora
% -------------------------- %
% 5 - Non-Associative Lambek Calculus
%     * Limitations
% 6 - Multi-modal Lambek Calculi
%     * NL_{CL}
%     * Moortgat (1996)
% 7 - Lambek-Grishin Calculus
%     * Algebraic + Translation
%     * Polarised + Translation
%

\begin{document}

\begin{abstract}
%include abstract.tex
\end{abstract}

%include introduction.tex
%include motivation.tex
%include agda_tutorial.tex
%include linguistic_data.tex

\nocite{*}
\bibliographystyle{apalike}
\bibliography{main}

\end{document}

%%% Local Variables:
%%% mode: latex
%%% TeX-master: t
%%% End:
