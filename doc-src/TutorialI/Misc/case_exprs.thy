(*<*)
theory case_exprs = Main:
(*>*)

subsection{*Case Expressions*}

text{*\label{sec:case-expressions}
HOL also features \sdx{case}-expressions for analyzing
elements of a datatype. For example,
@{term[display]"case xs of [] => 1 | y#ys => y"}
evaluates to @{term"1"} if @{term"xs"} is @{term"[]"} and to @{term"y"} if 
@{term"xs"} is @{term"y#ys"}. (Since the result in both branches must be of
the same type, it follows that @{term"y"} is of type @{typ"nat"} and hence
that @{term"xs"} is of type @{typ"nat list"}.)

In general, if $e$ is a term of the datatype $t$ defined in
\S\ref{sec:general-datatype} above, the corresponding
@{text"case"}-expression analyzing $e$ is
\[
\begin{array}{rrcl}
@{text"case"}~e~@{text"of"} & C@1~x@ {11}~\dots~x@ {1k@1} & \To & e@1 \\
                           \vdots \\
                           \mid & C@m~x@ {m1}~\dots~x@ {mk@m} & \To & e@m
\end{array}
\]

\begin{warn}
\emph{All} constructors must be present, their order is fixed, and nested
patterns are not supported.  Violating these restrictions results in strange
error messages.
\end{warn}
\noindent
Nested patterns can be simulated by nested @{text"case"}-expressions: instead
of
@{text[display]"case xs of [] => 1 | [x] => x | x # (y # zs) => y"}
write
@{term[display,eta_contract=false,margin=50]"case xs of [] => 1 | x#ys => (case ys of [] => x | y#zs => y)"}

Note that @{text"case"}-expressions may need to be enclosed in parentheses to
indicate their scope
*}

subsection{*Structural Induction and Case Distinction*}

text{*\label{sec:struct-ind-case}
\indexbold{structural induction}
\indexbold{induction!structural}
\indexbold{case distinction}
Almost all the basic laws about a datatype are applied automatically during
simplification. Only induction is invoked by hand via \methdx{induct_tac},
which works for any datatype. In some cases, induction is overkill and a case
distinction over all constructors of the datatype suffices. This is performed
by \methdx{case_tac}. A trivial example:
*}

lemma "(case xs of [] \<Rightarrow> [] | y#ys \<Rightarrow> xs) = xs";
apply(case_tac xs);

txt{*\noindent
results in the proof state
@{subgoals[display,indent=0,margin=65]}
which is solved automatically:
*}

apply(auto)
(*<*)done(*>*)
text{*
Note that we do not need to give a lemma a name if we do not intend to refer
to it explicitly in the future.

\begin{warn}
  Induction is only allowed on free (or \isasymAnd-bound) variables that
  should not occur among the assumptions of the subgoal; see
  \S\ref{sec:ind-var-in-prems} for details. Case distinction
  (@{text"case_tac"}) works for arbitrary terms, which need to be
  quoted if they are non-atomic. However, apart from @{text"\<And>"}-bound
  variables, the terms must not contain variables that are bound outside.
  For example, given the goal @{prop"\<forall>xs. xs = [] \<or> (\<exists>y ys. xs = y#ys)"},
  @{text"case_tac xs"} will not work as expected because Isabelle interprets
  the @{term xs} as a new free variable distinct from the bound
  @{term xs} in the goal.
\end{warn}
*}

(*<*)
end
(*>*)
