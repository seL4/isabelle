(*<*)
theory case_exprs imports Main begin
(*>*)

text{*
\subsection{Case Expressions}
\label{sec:case-expressions}\index{*case expressions}%
HOL also features \isa{case}-expressions for analyzing
elements of a datatype. For example,
@{term[display]"case xs of [] => [] | y#ys => y"}
evaluates to @{term"[]"} if @{term"xs"} is @{term"[]"} and to @{term"y"} if 
@{term"xs"} is @{term"y#ys"}. (Since the result in both branches must be of
the same type, it follows that @{term y} is of type @{typ"'a list"} and hence
that @{term xs} is of type @{typ"'a list list"}.)

In general, case expressions are of the form
\[
\begin{array}{c}
@{text"case"}~e~@{text"of"}\ pattern@1~@{text"\<Rightarrow>"}~e@1\ @{text"|"}\ \dots\
 @{text"|"}~pattern@m~@{text"\<Rightarrow>"}~e@m
\end{array}
\]
Like in functional programming, patterns are expressions consisting of
datatype constructors (e.g. @{term"[]"} and @{text"#"})
and variables, including the wildcard ``\verb$_$''.
Not all cases need to be covered and the order of cases matters.
However, one is well-advised not to wallow in complex patterns because
complex case distinctions tend to induce complex proofs.

\begin{warn}
Internally Isabelle only knows about exhaustive case expressions with
non-nested patterns: $pattern@i$ must be of the form
$C@i~x@ {i1}~\dots~x@ {ik@i}$ and $C@1, \dots, C@m$ must be exactly the
constructors of the type of $e$.
%
More complex case expressions are automatically
translated into the simpler form upon parsing but are not translated
back for printing. This may lead to surprising output.
\end{warn}

\begin{warn}
Like @{text"if"}, @{text"case"}-expressions may need to be enclosed in
parentheses to indicate their scope.
\end{warn}

\subsection{Structural Induction and Case Distinction}
\label{sec:struct-ind-case}
\index{case distinctions}\index{induction!structural}%
Induction is invoked by \methdx{induct_tac}, as we have seen above; 
it works for any datatype.  In some cases, induction is overkill and a case
distinction over all constructors of the datatype suffices.  This is performed
by \methdx{case_tac}.  Here is a trivial example:
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
Other basic laws about a datatype are applied automatically during
simplification, so no special methods are provided for them.

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
