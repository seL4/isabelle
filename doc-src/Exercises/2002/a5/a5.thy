(*<*)
theory a5 = Main:
(*>*)

subsection {* Merge sort *}

text {* Implement \emph{merge sort}: a list is sorted by splitting it
into two lists, sorting them separately, and merging the results.

With the help of @{text recdef} define two functions
*}

consts merge :: "nat list \<times> nat list \<Rightarrow> nat list"
       msort :: "nat list \<Rightarrow> nat list"

text {* and show *}

theorem "sorted (msort xs)"
(*<*)oops(*>*)

theorem "count (msort xs) x = count xs x"
(*<*)oops(*>*)

text {* where @{term sorted} and @{term count} are defined as in
section~\ref{psv2002a2}.

Hints:
\begin{itemize}
\item For @{text recdef} see section~3.5 of \cite{isabelle-tutorial}.

\item To split a list into two halves of almost equal length you can
use the functions \mbox{@{text "n div 2"}}, @{term take} und @{term drop},
where @{term "take n xs"} returns the first @{text n} elements of
@{text xs} and @{text "drop n xs"} the remainder.

\item Here are some potentially useful lemmas:\\
  @{text "linorder_not_le:"} @{thm linorder_not_le [no_vars]}\\
  @{text "order_less_le:"} @{thm order_less_le [no_vars]}\\
  @{text "min_def:"} @{thm min_def [no_vars]}
\end{itemize}
*}

(*<*)
end 
(*>*)
