(*<*)
theory cond_rewr = Main:;
(*>*)

text{*
So far all examples of rewrite rules were equations. The simplifier also
accepts \emph{conditional} equations, for example
*}

lemma hd_Cons_tl[simp]: "xs \\<noteq> []  \\<Longrightarrow>  hd xs # tl xs = xs";
apply(case_tac xs, simp, simp).;

text{*\noindent
Note the use of ``\ttindexboldpos{,}{$Isar}'' to string together a
sequence of methods. Assuming that the simplification rule
*}(*<*)term(*>*) "(rev xs = []) = (xs = [])";
text{*\noindent
is present as well,
*}

lemma "xs \\<noteq> [] \\<Longrightarrow> hd(rev xs) # tl(rev xs) = rev xs";
(*<*)
apply(simp).
(*>*)
text{*\noindent
is proved by plain simplification:
the conditional equation \isa{hd_Cons_tl} above
can simplify \isa{hd(rev~xs)~\#~tl(rev~xs)} to \isa{rev xs}
because the corresponding precondition \isa{rev xs \isasymnoteq\ []}
simplifies to \isa{xs \isasymnoteq\ []}, which is exactly the local
assumption of the subgoal.
*}
(*<*)
end
(*>*)
