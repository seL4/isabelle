(*<*)
theory Nested2 imports Nested0 begin
(*>*)

lemma [simp]: "t \<in> set ts \<longrightarrow> size t < Suc(term_list_size ts)"
by(induct_tac ts, auto)
(*<*)
recdef trev "measure size"
 "trev (Var x) = Var x"
 "trev (App f ts) = App f (rev(map trev ts))"
(*>*)
text{*\noindent
By making this theorem a simplification rule, \isacommand{recdef}
applies it automatically and the definition of @{term"trev"}
succeeds now. As a reward for our effort, we can now prove the desired
lemma directly.  We no longer need the verbose
induction schema for type @{text"term"} and can use the simpler one arising from
@{term"trev"}:
*}

lemma "trev(trev t) = t"
apply(induct_tac t rule: trev.induct)
txt{*
@{subgoals[display,indent=0]}
Both the base case and the induction step fall to simplification:
*}

by(simp_all add: rev_map sym[OF map_compose] cong: map_cong)

text{*\noindent
If the proof of the induction step mystifies you, we recommend that you go through
the chain of simplification steps in detail; you will probably need the help of
@{text"simp_trace"}. Theorem @{thm[source]map_cong} is discussed below.
%\begin{quote}
%{term[display]"trev(trev(App f ts))"}\\
%{term[display]"App f (rev(map trev (rev(map trev ts))))"}\\
%{term[display]"App f (map trev (rev(rev(map trev ts))))"}\\
%{term[display]"App f (map trev (map trev ts))"}\\
%{term[display]"App f (map (trev o trev) ts)"}\\
%{term[display]"App f (map (%x. x) ts)"}\\
%{term[display]"App f ts"}
%\end{quote}

The definition of @{term"trev"} above is superior to the one in
\S\ref{sec:nested-datatype} because it uses @{term"rev"}
and lets us use existing facts such as \hbox{@{prop"rev(rev xs) = xs"}}.
Thus this proof is a good example of an important principle:
\begin{quote}
\emph{Chose your definitions carefully\\
because they determine the complexity of your proofs.}
\end{quote}

Let us now return to the question of how \isacommand{recdef} can come up with
sensible termination conditions in the presence of higher-order functions
like @{term"map"}. For a start, if nothing were known about @{term"map"}, then
@{term"map trev ts"} might apply @{term"trev"} to arbitrary terms, and thus
\isacommand{recdef} would try to prove the unprovable @{term"size t < Suc
(term_list_size ts)"}, without any assumption about @{term"t"}.  Therefore
\isacommand{recdef} has been supplied with the congruence theorem
@{thm[source]map_cong}:
@{thm[display,margin=50]"map_cong"[no_vars]}
Its second premise expresses that in @{term"map f xs"},
function @{term"f"} is only applied to elements of list @{term"xs"}.  Congruence
rules for other higher-order functions on lists are similar.  If you get
into a situation where you need to supply \isacommand{recdef} with new
congruence rules, you can append a hint after the end of
the recursion equations:\cmmdx{hints}
*}
(*<*)
consts dummy :: "nat => nat"
recdef dummy "{}"
"dummy n = n"
(*>*)
(hints recdef_cong: map_cong)

text{*\noindent
Or you can declare them globally
by giving them the \attrdx{recdef_cong} attribute:
*}

declare map_cong[recdef_cong]

text{*
The @{text cong} and @{text recdef_cong} attributes are
intentionally kept apart because they control different activities, namely
simplification and making recursive definitions.
%The simplifier's congruence rules cannot be used by recdef.
%For example the weak congruence rules for if and case would prevent
%recdef from generating sensible termination conditions.
*}
(*<*)end(*>*)
