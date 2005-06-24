(*<*)
theory find2 imports Main begin
lemma "A \<and> B"
(*>*)

txt{*\index{finding theorems}\index{searching theorems} In
\S\ref{sec:find}, we introduced Proof General's \pgmenu{Find} button
for finding theorems in the database via pattern matching. If we are
inside a proof, we can be more specific; we can search for introduction,
elimination and destruction rules \emph{with respect to the current goal}.
For this purpose, \pgmenu{Find} provides three aditional search criteria:
\texttt{intro}, \texttt{elim} and \texttt{dest}.

For example, given the goal @{subgoals[display,indent=0,margin=65]}
you can click on \pgmenu{Find} and type in the search expression
\texttt{intro}. You will be shown a few rules ending in @{text"\<Longrightarrow> ?P \<and> ?Q"},
among them @{thm[source]conjI}\@. You may even discover that
the very theorem you are trying to prove is already in the
database.  Given the goal *}
(*<*)
oops
lemma "A \<longrightarrow> A"
(*>*)
txt{*\vspace{-\bigskipamount}
@{subgoals[display,indent=0,margin=65]}
the search for \texttt{intro} finds not just @{thm[source] impI}
but also @{thm[source] imp_refl}: @{thm imp_refl}.

As before, search criteria can be combined freely: for example,
\begin{ttbox}
"_ \at\ _"  intro
\end{ttbox}
searches for all introduction rules that match the current goal and
mention the @{text"@"} function.

Searching for elimination and destruction rules via \texttt{elim} and
\texttt{dest} is analogous to \texttt{intro} but takes the assumptions
into account, too.
*}
(*<*)
oops
end
(*>*)
