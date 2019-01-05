(*<*)
theory case_exprs imports Main begin
(*>*)

text\<open>
\subsection{Case Expressions}
\label{sec:case-expressions}\index{*case expressions}%
HOL also features \isa{case}-expressions for analyzing
elements of a datatype. For example,
@{term[display]"case xs of [] => [] | y#ys => y"}
evaluates to \<^term>\<open>[]\<close> if \<^term>\<open>xs\<close> is \<^term>\<open>[]\<close> and to \<^term>\<open>y\<close> if 
\<^term>\<open>xs\<close> is \<^term>\<open>y#ys\<close>. (Since the result in both branches must be of
the same type, it follows that \<^term>\<open>y\<close> is of type \<^typ>\<open>'a list\<close> and hence
that \<^term>\<open>xs\<close> is of type \<^typ>\<open>'a list list\<close>.)

In general, case expressions are of the form
\[
\begin{array}{c}
\<open>case\<close>~e~\<open>of\<close>\ pattern@1~\<open>\<Rightarrow>\<close>~e@1\ \<open>|\<close>\ \dots\
 \<open>|\<close>~pattern@m~\<open>\<Rightarrow>\<close>~e@m
\end{array}
\]
Like in functional programming, patterns are expressions consisting of
datatype constructors (e.g. \<^term>\<open>[]\<close> and \<open>#\<close>)
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
Like \<open>if\<close>, \<open>case\<close>-expressions may need to be enclosed in
parentheses to indicate their scope.
\end{warn}

\subsection{Structural Induction and Case Distinction}
\label{sec:struct-ind-case}
\index{case distinctions}\index{induction!structural}%
Induction is invoked by \methdx{induct_tac}, as we have seen above; 
it works for any datatype.  In some cases, induction is overkill and a case
distinction over all constructors of the datatype suffices.  This is performed
by \methdx{case_tac}.  Here is a trivial example:
\<close>

lemma "(case xs of [] \<Rightarrow> [] | y#ys \<Rightarrow> xs) = xs"
apply(case_tac xs)

txt\<open>\noindent
results in the proof state
@{subgoals[display,indent=0,margin=65]}
which is solved automatically:
\<close>

apply(auto)
(*<*)done(*>*)
text\<open>
Note that we do not need to give a lemma a name if we do not intend to refer
to it explicitly in the future.
Other basic laws about a datatype are applied automatically during
simplification, so no special methods are provided for them.

\begin{warn}
  Induction is only allowed on free (or \isasymAnd-bound) variables that
  should not occur among the assumptions of the subgoal; see
  \S\ref{sec:ind-var-in-prems} for details. Case distinction
  (\<open>case_tac\<close>) works for arbitrary terms, which need to be
  quoted if they are non-atomic. However, apart from \<open>\<And>\<close>-bound
  variables, the terms must not contain variables that are bound outside.
  For example, given the goal \<^prop>\<open>\<forall>xs. xs = [] \<or> (\<exists>y ys. xs = y#ys)\<close>,
  \<open>case_tac xs\<close> will not work as expected because Isabelle interprets
  the \<^term>\<open>xs\<close> as a new free variable distinct from the bound
  \<^term>\<open>xs\<close> in the goal.
\end{warn}
\<close>

(*<*)
end
(*>*)
