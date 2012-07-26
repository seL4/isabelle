(*<*)
theory pairs2 imports Main begin;
(*>*)
text{*\label{sec:pairs}\index{pairs and tuples}
HOL also has ordered pairs: \isa{($a@1$,$a@2$)} is of type $\tau@1$
\indexboldpos{\isasymtimes}{$Isatype} $\tau@2$ provided each $a@i$ is of type
$\tau@i$. The functions \cdx{fst} and
\cdx{snd} extract the components of a pair:
 \isa{fst($x$,$y$) = $x$} and \isa{snd($x$,$y$) = $y$}. Tuples
are simulated by pairs nested to the right: \isa{($a@1$,$a@2$,$a@3$)} stands
for \isa{($a@1$,($a@2$,$a@3$))} and $\tau@1 \times \tau@2 \times \tau@3$ for
$\tau@1 \times (\tau@2 \times \tau@3)$. Therefore we have
\isa{fst(snd($a@1$,$a@2$,$a@3$)) = $a@2$}.

Remarks:
\begin{itemize}
\item
There is also the type \tydx{unit}, which contains exactly one
element denoted by~\cdx{()}.  This type can be viewed
as a degenerate product with 0 components.
\item
Products, like type @{typ nat}, are datatypes, which means
in particular that @{text induct_tac} and @{text case_tac} are applicable to
terms of product type.
Both split the term into a number of variables corresponding to the tuple structure
(up to 7 components).
\item
Tuples with more than two or three components become unwieldy;
records are preferable.
\end{itemize}
For more information on pairs and records see Chapter~\ref{ch:more-types}.
*}
(*<*)
end
(*>*)
