(*<*)
theory asm_simp = Main:;

(*>*)text{*
By default, assumptions are part of the simplification process: they are used
as simplification rules and are simplified themselves. For example:
*}

lemma "\\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \\<rbrakk> \\<Longrightarrow> ys = zs";
by simp;

text{*\noindent
The second assumption simplifies to @{term"xs = []"}, which in turn
simplifies the first assumption to @{term"zs = ys"}, thus reducing the
conclusion to @{term"ys = ys"} and hence to \isa{True}.

In some cases this may be too much of a good thing and may lead to
nontermination:
*}

lemma "\\<forall>x. f x = g (f (g x)) \\<Longrightarrow> f [] = f [] @ []";

txt{*\noindent
cannot be solved by an unmodified application of \isa{simp} because the
simplification rule @{term"f x = g (f (g x))"} extracted from the assumption
does not terminate. Isabelle notices certain simple forms of
nontermination but not this one. The problem can be circumvented by
explicitly telling the simplifier to ignore the assumptions:
*}

by(simp (no_asm));

text{*\noindent
There are three options that influence the treatment of assumptions:
\begin{description}
\item[\isa{(no_asm)}]\indexbold{*no_asm}
 means that assumptions are completely ignored.
\item[\isa{(no_asm_simp)}]\indexbold{*no_asm_simp}
 means that the assumptions are not simplified but
  are used in the simplification of the conclusion.
\item[\isa{(no_asm_use)}]\indexbold{*no_asm_use}
 means that the assumptions are simplified but are not
  used in the simplification of each other or the conclusion.
\end{description}
Neither \isa{(no_asm_simp)} nor \isa{(no_asm_use)} allow to simplify the above
problematic subgoal.

Note that only one of the above options is allowed, and it must precede all
other arguments.
*}
(*<*)end(*>*)
