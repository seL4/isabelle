(*<*)
theory trace_simp = Main:;
(*>*)

text{*
Using the simplifier effectively may take a bit of experimentation.  Set the
\ttindexbold{trace_simp} \rmindex{flag} to get a better idea of what is going
on:
*}
ML "set trace_simp";
lemma "rev [a] = []";
apply(simp);

txt{*\noindent
produces the trace

\begin{ttbox}
Applying instance of rewrite rule:
rev (?x1 \# ?xs1) == rev ?xs1 @ [?x1]
Rewriting:
rev [x] == rev [] @ [x]
Applying instance of rewrite rule:
rev [] == []
Rewriting:
rev [] == []
Applying instance of rewrite rule:
[] @ ?y == ?y
Rewriting:
[] @ [x] == [x]
Applying instance of rewrite rule:
?x3 \# ?t3 = ?t3 == False
Rewriting:
[x] = [] == False
\end{ttbox}

In more complicated cases, the trace can quite lenghty, especially since
invocations of the simplifier are often nested (e.g.\ when solving conditions
of rewrite rules). Thus it is advisable to reset it:
*}

ML "reset trace_simp";

(*<*)
oops;
end
(*>*)
