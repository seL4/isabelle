(*<*)
theory case_splits = Main:;
(*>*)

text{*
Goals containing \isaindex{if}-expressions are usually proved by case
distinction on the condition of the \isa{if}. For example the goal
*}

lemma "\\<forall>xs. if xs = [] then rev xs = [] else rev xs \\<noteq> []";

txt{*\noindent
can be split into
\begin{isabellepar}%
~1.~{\isasymforall}xs.~(xs~=~[]~{\isasymlongrightarrow}~rev~xs~=~[])~{\isasymand}~(xs~{\isasymnoteq}~[]~{\isasymlongrightarrow}~rev~xs~{\isasymnoteq}~[])%
\end{isabellepar}%
by a degenerate form of simplification
*}

apply(simp only: split: split_if);
(*<*)oops;(*>*)

text{*\noindent
where no simplification rules are included (\isa{only:} is followed by the
empty list of theorems) but the rule \isaindexbold{split_if} for
splitting \isa{if}s is added (via the modifier \isa{split:}). Because
case-splitting on \isa{if}s is almost always the right proof strategy, the
simplifier performs it automatically. Try \isacommand{apply}\isa{(simp)}
on the initial goal above.

This splitting idea generalizes from \isa{if} to \isaindex{case}:
*}

lemma "(case xs of [] \\<Rightarrow> zs | y#ys \\<Rightarrow> y#(ys@zs)) = xs@zs";
txt{*\noindent
becomes
\begin{isabellepar}%
~1.~(xs~=~[]~{\isasymlongrightarrow}~zs~=~xs~@~zs)~{\isasymand}\isanewline
~~~~({\isasymforall}a~list.~xs~=~a~\#~list~{\isasymlongrightarrow}~a~\#~list~@~zs~=~xs~@~zs)%
\end{isabellepar}%
by typing
*}

apply(simp only: split: list.split);
(*<*)oops;(*>*)

text{*\noindent
In contrast to \isa{if}-expressions, the simplifier does not split
\isa{case}-expressions by default because this can lead to nontermination
in case of recursive datatypes. Again, if the \isa{only:} modifier is
dropped, the above goal is solved,
*}
(*<*)
lemma "(case xs of [] \\<Rightarrow> zs | y#ys \\<Rightarrow> y#(ys@zs)) = xs@zs";
(*>*)
by(simp split: list.split);

text{*\noindent%
which \isacommand{apply}\isa{(simp)} alone will not do.

In general, every datatype $t$ comes with a theorem
\isa{$t$.split} which can be declared to be a \bfindex{split rule} either
locally as above, or by giving it the \isa{split} attribute globally:
*}

theorems [split] = list.split;

text{*\noindent
The \isa{split} attribute can be removed with the \isa{del} modifier,
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
theorems [split del] = list.split;

(*<*)
end
(*>*)
