(*<*)
theory "cases" = Main:;
(*>*)

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

by(auto);
(**)
(*<*)
end
(*>*)
