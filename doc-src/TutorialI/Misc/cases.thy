(*<*)
theory "cases" = Main:;
(*>*)

subsection{*Structural induction and case distinction*}

text{*
\indexbold{structural induction}
\indexbold{induction!structural}
\indexbold{case distinction}
Almost all the basic laws about a datatype are applied automatically during
simplification. Only induction is invoked by hand via \isaindex{induct_tac},
which works for any datatype. In some cases, induction is overkill and a case
distinction over all constructors of the datatype suffices. This is performed
by \isaindexbold{case_tac}. A trivial example:
*}

lemma "(case xs of [] \\<Rightarrow> [] | y#ys \\<Rightarrow> xs) = xs";
apply(case_tac xs);

txt{*\noindent
results in the proof state
\begin{isabellepar}%
~1.~xs~=~[]~{\isasymLongrightarrow}~(case~xs~of~[]~{\isasymRightarrow}~[]~|~y~\#~ys~{\isasymRightarrow}~xs)~=~xs\isanewline
~2.~{\isasymAnd}a~list.~xs=a\#list~{\isasymLongrightarrow}~(case~xs~of~[]~{\isasymRightarrow}~[]~|~y\#ys~{\isasymRightarrow}~xs)~=~xs%
\end{isabellepar}%
which is solved automatically:
*}

by(auto)

text{*
Note that we do not need to give a lemma a name if we do not intend to refer
to it explicitly in the future.
*}

(*<*)
end
(*>*)
