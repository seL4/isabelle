(*<*)
theory natsum = Main:;
(*>*)
text{*\noindent
In particular, there are @{text"case"}-expressions, for example
@{term[display]"case n of 0 => 0 | Suc m => m"}
primitive recursion, for example
*}

consts sum :: "nat \<Rightarrow> nat";
primrec "sum 0 = 0"
        "sum (Suc n) = Suc n + sum n";

text{*\noindent
and induction, for example
*}

lemma "sum n + sum n = n*(Suc n)";
apply(induct_tac n);
apply(auto);
done

text{*\newcommand{\mystar}{*%
}
The usual arithmetic operations \ttindexboldpos{+}{$HOL2arithfun},
\ttindexboldpos{-}{$HOL2arithfun}, \ttindexboldpos{\mystar}{$HOL2arithfun},
\isaindexbold{div}, \isaindexbold{mod}, \isaindexbold{min} and
\isaindexbold{max} are predefined, as are the relations
\indexboldpos{\isasymle}{$HOL2arithrel} and
\ttindexboldpos{<}{$HOL2arithrel}. As usual, @{prop"m-n = 0"} if
@{prop"m<n"}. There is even a least number operation
\isaindexbold{LEAST}. For example, @{prop"(LEAST n. 1 < n) = 2"}, although
Isabelle does not prove this completely automatically. Note that @{term 1}
and @{term 2} are available as abbreviations for the corresponding
@{term Suc}-expressions. If you need the full set of numerals,
see~\S\ref{sec:numerals}.

\begin{warn}
  The constant \ttindexbold{0} and the operations
  \ttindexboldpos{+}{$HOL2arithfun}, \ttindexboldpos{-}{$HOL2arithfun},
  \ttindexboldpos{\mystar}{$HOL2arithfun}, \isaindexbold{min},
  \isaindexbold{max}, \indexboldpos{\isasymle}{$HOL2arithrel} and
  \ttindexboldpos{<}{$HOL2arithrel} are overloaded, i.e.\ they are available
  not just for natural numbers but at other types as well (see
  \S\ref{sec:overloading}). For example, given the goal @{prop"x+0 = x"},
  there is nothing to indicate that you are talking about natural numbers.
  Hence Isabelle can only infer that @{term x} is of some arbitrary type where
  @{term 0} and @{text"+"} are declared. As a consequence, you will be unable
  to prove the goal (although it may take you some time to realize what has
  happened if @{text show_types} is not set).  In this particular example,
  you need to include an explicit type constraint, for example
  @{text"x+0 = (x::nat)"}. If there is enough contextual information this
  may not be necessary: @{prop"Suc x = x"} automatically implies
  @{text"x::nat"} because @{term Suc} is not overloaded.
\end{warn}

Simple arithmetic goals are proved automatically by both @{term auto} and the
simplification methods introduced in \S\ref{sec:Simplification}.  For
example,
*}

lemma "\<lbrakk> \<not> m < n; m < n+1 \<rbrakk> \<Longrightarrow> m = n"
(*<*)by(auto)(*>*)

text{*\noindent
is proved automatically. The main restriction is that only addition is taken
into account; other arithmetic operations and quantified formulae are ignored.

For more complex goals, there is the special method \isaindexbold{arith}
(which attacks the first subgoal). It proves arithmetic goals involving the
usual logical connectives (@{text"\<not>"}, @{text"\<and>"}, @{text"\<or>"},
@{text"\<longrightarrow>"}), the relations @{text"="}, @{text"\<le>"} and @{text"<"},
and the operations
@{text"+"}, @{text"-"}, @{term min} and @{term max}. Technically, this is
known as the class of (quantifier free) \bfindex{linear arithmetic} formulae.
For example,
*}

lemma "min i (max j (k*k)) = max (min (k*k) i) (min i (j::nat))";
apply(arith)
(*<*)done(*>*)

text{*\noindent
succeeds because @{term"k*k"} can be treated as atomic. In contrast,
*}

lemma "n*n = n \<Longrightarrow> n=0 \<or> n=1"
(*<*)oops(*>*)

text{*\noindent
is not even proved by @{text arith} because the proof relies essentially
on properties of multiplication.

\begin{warn}
  The running time of @{text arith} is exponential in the number of occurrences
  of \ttindexboldpos{-}{$HOL2arithfun}, \isaindexbold{min} and
  \isaindexbold{max} because they are first eliminated by case distinctions.

  \isa{arith} is incomplete even for the restricted class of
  linear arithmetic formulae. If divisibility plays a
  role, it may fail to prove a valid formula, for example
  @{prop"m+m \<noteq> n+n+1"}. Fortunately, such examples are rare in practice.
\end{warn}
*}

(*<*)
end
(*>*)
