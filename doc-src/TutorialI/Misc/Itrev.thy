(*<*)
theory Itrev = Main:;
(*>*)

text{* Function \isa{rev} has quadratic worst-case running time
because it calls function \isa{\at} for each element of the list and
\isa{\at} is linear in its first argument.  A linear time version of
\isa{rev} reqires an extra argument where the result is accumulated
gradually, using only \isa{\#}:*}

consts itrev :: "'a list \\<Rightarrow> 'a list \\<Rightarrow> 'a list";
primrec
"itrev []     ys = ys"
"itrev (x#xs) ys = itrev xs (x#ys)";

text{*\noindent The behaviour of \isa{itrev} is simple: it reverses
its first argument by stacking its elements onto the second argument,
and returning that second argument when the first one becomes
empty. Note that \isa{itrev} is tail-recursive, i.e.\ it can be
compiled into a loop.

Naturally, we would like to show that \isa{itrev} does indeed reverse
its first argument provided the second one is empty: *};

lemma "itrev xs [] = rev xs";

txt{*\noindent
There is no choice as to the induction variable, and we immediately simplify:
*};

apply(induct_tac xs, auto);

txt{*\noindent
Unfortunately, this is not a complete success:
\begin{isabellepar}%
~1.~\dots~itrev~list~[]~=~rev~list~{\isasymLongrightarrow}~itrev~list~[a]~=~rev~list~@~[a]%
\end{isabellepar}%
Just as predicted above, the overall goal, and hence the induction
hypothesis, is too weak to solve the induction step because of the fixed
\isa{[]}. The corresponding heuristic:
\begin{quote}
{\em 3. Generalize goals for induction by replacing constants by variables.}
\end{quote}

Of course one cannot do this na\"{\i}vely: \isa{itrev xs ys = rev xs} is
just not true---the correct generalization is
*};
(*<*)oops;(*>*)
lemma "itrev xs ys = rev xs @ ys";

txt{*\noindent
If \isa{ys} is replaced by \isa{[]}, the right-hand side simplifies to
@{term"rev xs"}, just as required.

In this particular instance it was easy to guess the right generalization,
but in more complex situations a good deal of creativity is needed. This is
the main source of complications in inductive proofs.

Although we now have two variables, only \isa{xs} is suitable for
induction, and we repeat our above proof attempt. Unfortunately, we are still
not there:
\begin{isabellepar}%
~1.~{\isasymAnd}a~list.\isanewline
~~~~~~~itrev~list~ys~=~rev~list~@~ys~{\isasymLongrightarrow}\isanewline
~~~~~~~itrev~list~(a~\#~ys)~=~rev~list~@~a~\#~ys%
\end{isabellepar}%
The induction hypothesis is still too weak, but this time it takes no
intuition to generalize: the problem is that \isa{ys} is fixed throughout
the subgoal, but the induction hypothesis needs to be applied with
@{term"a # ys"} instead of \isa{ys}. Hence we prove the theorem
for all \isa{ys} instead of a fixed one:
*};
(*<*)oops;(*>*)
lemma "\\<forall>ys. itrev xs ys = rev xs @ ys";

txt{*\noindent
This time induction on \isa{xs} followed by simplification succeeds. This
leads to another heuristic for generalization:
\begin{quote}
{\em 4. Generalize goals for induction by universally quantifying all free
variables {\em(except the induction variable itself!)}.}
\end{quote}
This prevents trivial failures like the above and does not change the
provability of the goal. Because it is not always required, and may even
complicate matters in some cases, this heuristic is often not
applied blindly.
*};

(*<*)
by(induct_tac xs, simp, simp);
end
(*>*)
