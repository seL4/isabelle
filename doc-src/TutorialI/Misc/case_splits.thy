(*<*)
theory case_splits = Main:;
(*>*)

text{*
Goals containing @{text"if"}-expressions are usually proved by case
distinction on the condition of the @{text"if"}. For example the goal
*}

lemma "\\<forall>xs. if xs = [] then rev xs = [] else rev xs \\<noteq> []";

txt{*\noindent
can be split into
\begin{isabelle}
~1.~{\isasymforall}xs.~(xs~=~[]~{\isasymlongrightarrow}~rev~xs~=~[])~{\isasymand}~(xs~{\isasymnoteq}~[]~{\isasymlongrightarrow}~rev~xs~{\isasymnoteq}~[])
\end{isabelle}
by a degenerate form of simplification
*}

apply(simp only: split: split_if);
(*<*)oops;(*>*)

text{*\noindent
where no simplification rules are included (@{text"only:"} is followed by the
empty list of theorems) but the rule \isaindexbold{split_if} for
splitting @{text"if"}s is added (via the modifier @{text"split:"}). Because
case-splitting on @{text"if"}s is almost always the right proof strategy, the
simplifier performs it automatically. Try \isacommand{apply}@{text"(simp)"}
on the initial goal above.

This splitting idea generalizes from @{text"if"} to \isaindex{case}:
*}

lemma "(case xs of [] \\<Rightarrow> zs | y#ys \\<Rightarrow> y#(ys@zs)) = xs@zs";
txt{*\noindent
becomes
\begin{isabelle}
~1.~(xs~=~[]~{\isasymlongrightarrow}~zs~=~xs~@~zs)~{\isasymand}\isanewline
~~~~({\isasymforall}a~list.~xs~=~a~\#~list~{\isasymlongrightarrow}~a~\#~list~@~zs~=~xs~@~zs)
\end{isabelle}
by typing
*}

apply(simp only: split: list.split);
(*<*)oops;(*>*)

text{*\noindent
In contrast to @{text"if"}-expressions, the simplifier does not split
@{text"case"}-expressions by default because this can lead to nontermination
in case of recursive datatypes. Again, if the @{text"only:"} modifier is
dropped, the above goal is solved,
*}
(*<*)
lemma "(case xs of [] \\<Rightarrow> zs | y#ys \\<Rightarrow> y#(ys@zs)) = xs@zs";
(*>*)
by(simp split: list.split);

text{*\noindent%
which \isacommand{apply}@{text"(simp)"} alone will not do.

In general, every datatype $t$ comes with a theorem
$t$@{text".split"} which can be declared to be a \bfindex{split rule} either
locally as above, or by giving it the @{text"split"} attribute globally:
*}

lemmas [split] = list.split;

text{*\noindent
The @{text"split"} attribute can be removed with the @{text"del"} modifier,
either locally
*}
(*<*)
lemma "dummy=dummy";
(*>*)
apply(simp split del: split_if);
(*<*)
oops;
(*>*)
text{*\noindent
or globally:
*}
lemmas [split del] = list.split;

text{*
The above split rules intentionally only affect the conclusion of a
subgoal.  If you want to split an @{text"if"} or @{text"case"}-expression in
the assumptions, you have to apply @{thm[source]split_if_asm} or
$t$@{text".split_asm"}:
*}

lemma "if xs = [] then ys ~= [] else ys = [] ==> xs @ ys ~= []"
apply(simp only: split: split_if_asm);

txt{*\noindent
In contrast to splitting the conclusion, this actually creates two
separate subgoals (which are solved by @{text"simp_all"}):
\begin{isabelle}
\ \isadigit{1}{\isachardot}\ {\isasymlbrakk}\mbox{xs}\ {\isacharequal}\ {\isacharbrackleft}{\isacharbrackright}{\isacharsemicolon}\ \mbox{ys}\ {\isasymnoteq}\ {\isacharbrackleft}{\isacharbrackright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ {\isacharbrackleft}{\isacharbrackright}\ {\isacharat}\ \mbox{ys}\ {\isasymnoteq}\ {\isacharbrackleft}{\isacharbrackright}\isanewline
\ \isadigit{2}{\isachardot}\ {\isasymlbrakk}\mbox{xs}\ {\isasymnoteq}\ {\isacharbrackleft}{\isacharbrackright}{\isacharsemicolon}\ \mbox{ys}\ {\isacharequal}\ {\isacharbrackleft}{\isacharbrackright}{\isasymrbrakk}\ {\isasymLongrightarrow}\ \mbox{xs}\ {\isacharat}\ {\isacharbrackleft}{\isacharbrackright}\ {\isasymnoteq}\ {\isacharbrackleft}{\isacharbrackright}
\end{isabelle}
If you need to split both in the assumptions and the conclusion,
use $t$@{text".splits"} which subsumes $t$@{text".split"} and
$t$@{text".split_asm"}. Analogously, there is @{thm[source]if_splits}.
*}

(*<*)
by(simp_all)
end
(*>*)
