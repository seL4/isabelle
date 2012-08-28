(*<*)
theory Itrev
imports Main
begin
declare [[names_unique = false]]
(*>*)

section{*Induction Heuristics*}

text{*\label{sec:InductionHeuristics}
\index{induction heuristics|(}%
The purpose of this section is to illustrate some simple heuristics for
inductive proofs. The first one we have already mentioned in our initial
example:
\begin{quote}
\emph{Theorems about recursive functions are proved by induction.}
\end{quote}
In case the function has more than one argument
\begin{quote}
\emph{Do induction on argument number $i$ if the function is defined by
recursion in argument number $i$.}
\end{quote}
When we look at the proof of @{text"(xs@ys) @ zs = xs @ (ys@zs)"}
in \S\ref{sec:intro-proof} we find
\begin{itemize}
\item @{text"@"} is recursive in
the first argument
\item @{term xs}  occurs only as the first argument of
@{text"@"}
\item both @{term ys} and @{term zs} occur at least once as
the second argument of @{text"@"}
\end{itemize}
Hence it is natural to perform induction on~@{term xs}.

The key heuristic, and the main point of this section, is to
\emph{generalize the goal before induction}.
The reason is simple: if the goal is
too specific, the induction hypothesis is too weak to allow the induction
step to go through. Let us illustrate the idea with an example.

Function \cdx{rev} has quadratic worst-case running time
because it calls function @{text"@"} for each element of the list and
@{text"@"} is linear in its first argument.  A linear time version of
@{term"rev"} reqires an extra argument where the result is accumulated
gradually, using only~@{text"#"}:
*}

primrec itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev []     ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

text{*\noindent
The behaviour of \cdx{itrev} is simple: it reverses
its first argument by stacking its elements onto the second argument,
and returning that second argument when the first one becomes
empty. Note that @{term"itrev"} is tail-recursive: it can be
compiled into a loop.

Naturally, we would like to show that @{term"itrev"} does indeed reverse
its first argument provided the second one is empty:
*};

lemma "itrev xs [] = rev xs";

txt{*\noindent
There is no choice as to the induction variable, and we immediately simplify:
*};

apply(induct_tac xs, simp_all);

txt{*\noindent
Unfortunately, this attempt does not prove
the induction step:
@{subgoals[display,indent=0,margin=70]}
The induction hypothesis is too weak.  The fixed
argument,~@{term"[]"}, prevents it from rewriting the conclusion.  
This example suggests a heuristic:
\begin{quote}\index{generalizing induction formulae}%
\emph{Generalize goals for induction by replacing constants by variables.}
\end{quote}
Of course one cannot do this na\"{\i}vely: @{term"itrev xs ys = rev xs"} is
just not true.  The correct generalization is
*};
(*<*)oops;(*>*)
lemma "itrev xs ys = rev xs @ ys";
(*<*)apply(induct_tac xs, simp_all)(*>*)
txt{*\noindent
If @{term"ys"} is replaced by @{term"[]"}, the right-hand side simplifies to
@{term"rev xs"}, as required.

In this instance it was easy to guess the right generalization.
Other situations can require a good deal of creativity.  

Although we now have two variables, only @{term"xs"} is suitable for
induction, and we repeat our proof attempt. Unfortunately, we are still
not there:
@{subgoals[display,indent=0,goals_limit=1]}
The induction hypothesis is still too weak, but this time it takes no
intuition to generalize: the problem is that @{term"ys"} is fixed throughout
the subgoal, but the induction hypothesis needs to be applied with
@{term"a # ys"} instead of @{term"ys"}. Hence we prove the theorem
for all @{term"ys"} instead of a fixed one:
*};
(*<*)oops;(*>*)
lemma "\<forall>ys. itrev xs ys = rev xs @ ys";
(*<*)
by(induct_tac xs, simp_all);
(*>*)

text{*\noindent
This time induction on @{term"xs"} followed by simplification succeeds. This
leads to another heuristic for generalization:
\begin{quote}
\emph{Generalize goals for induction by universally quantifying all free
variables {\em(except the induction variable itself!)}.}
\end{quote}
This prevents trivial failures like the one above and does not affect the
validity of the goal.  However, this heuristic should not be applied blindly.
It is not always required, and the additional quantifiers can complicate
matters in some cases. The variables that should be quantified are typically
those that change in recursive calls.

A final point worth mentioning is the orientation of the equation we just
proved: the more complex notion (@{const itrev}) is on the left-hand
side, the simpler one (@{term rev}) on the right-hand side. This constitutes
another, albeit weak heuristic that is not restricted to induction:
\begin{quote}
  \emph{The right-hand side of an equation should (in some sense) be simpler
    than the left-hand side.}
\end{quote}
This heuristic is tricky to apply because it is not obvious that
@{term"rev xs @ ys"} is simpler than @{term"itrev xs ys"}. But see what
happens if you try to prove @{prop"rev xs @ ys = itrev xs ys"}!

If you have tried these heuristics and still find your
induction does not go through, and no obvious lemma suggests itself, you may
need to generalize your proposition even further. This requires insight into
the problem at hand and is beyond simple rules of thumb.  
Additionally, you can read \S\ref{sec:advanced-ind}
to learn about some advanced techniques for inductive proofs.%
\index{induction heuristics|)}
*}
(*<*)
declare [[names_unique = true]]
end
(*>*)
