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
\index{arithmetic operations!for \protect\isa{nat}}%
The arithmetic operations \ttindexboldpos{+}{$HOL2arithfun},
\ttindexboldpos{-}{$HOL2arithfun}, \ttindexboldpos{\mystar}{$HOL2arithfun},
\sdx{div}, \sdx{mod}, \cdx{min} and
\cdx{max} are predefined, as are the relations
\indexboldpos{\isasymle}{$HOL2arithrel} and
\ttindexboldpos{<}{$HOL2arithrel}. As usual, @{prop"m-n = (0::nat)"} if
@{prop"m<n"}. There is even a least number operation
\sdx{LEAST}\@.  For example, @{prop"(LEAST n. 0 < n) = Suc 0"}.
\begin{warn}\index{overloading}
  The constants \cdx{0} and \cdx{1} and the operations
  \ttindexboldpos{+}{$HOL2arithfun}, \ttindexboldpos{-}{$HOL2arithfun},
  \ttindexboldpos{\mystar}{$HOL2arithfun}, \cdx{min},
  \cdx{max}, \indexboldpos{\isasymle}{$HOL2arithrel} and
  \ttindexboldpos{<}{$HOL2arithrel} are overloaded: they are available
  not just for natural numbers but for other types as well.
  For example, given the goal @{text"x + 0 = x"}, there is nothing to indicate
  that you are talking about natural numbers. Hence Isabelle can only infer
  that @{term x} is of some arbitrary type where @{text 0} and @{text"+"} are
  declared. As a consequence, you will be unable to prove the
  goal. To alert you to such pitfalls, Isabelle flags numerals without a
  fixed type in its output: @{prop"x+0 = x"}. (In the absence of a numeral,
  it may take you some time to realize what has happened if @{text
  show_types} is not set).  In this particular example, you need to include
  an explicit type constraint, for example @{text"x+0 = (x::nat)"}. If there
  is enough contextual information this may not be necessary: @{prop"Suc x =
  x"} automatically implies @{text"x::nat"} because @{term Suc} is not
  overloaded.

  For details on overloading see \S\ref{sec:overloading}.
  Table~\ref{tab:overloading} in the appendix shows the most important
  overloaded operations.
\end{warn}
\begin{warn}
  Constant @{text"1::nat"} is defined to equal @{term"Suc 0"}. This definition
  (see \S\ref{sec:ConstDefinitions}) is unfolded automatically by some
  tactics (like @{text auto}, @{text simp} and @{text arith}) but not by
  others (especially the single step tactics in Chapter~\ref{chap:rules}).
  If you need the full set of numerals, see~\S\ref{sec:numerals}.
  \emph{Novices are advised to stick to @{term"0::nat"} and @{term Suc}.}
\end{warn}

Both @{text auto} and @{text simp}
(a method introduced below, \S\ref{sec:Simplification}) prove 
simple arithmetic goals automatically:
*}

lemma "\<lbrakk> \<not> m < n; m < n + (1::nat) \<rbrakk> \<Longrightarrow> m = n"
(*<*)by(auto)(*>*)

text{*\noindent
For efficiency's sake, this built-in prover ignores quantified formulae,
logical connectives, and all arithmetic operations apart from addition.
In consequence, @{text auto} cannot prove this slightly more complex goal:
*}

lemma "\<not> m < n \<and> m < n + (1::nat) \<Longrightarrow> m = n";
(*<*)by(arith)(*>*)

text{*\noindent
The method \methdx{arith} is more general.  It attempts to prove
the first subgoal provided it is a quantifier-free \textbf{linear arithmetic}
formula.  Such formulas may involve the
usual logical connectives (@{text"\<not>"}, @{text"\<and>"}, @{text"\<or>"},
@{text"\<longrightarrow>"}), the relations @{text"="}, @{text"\<le>"} and @{text"<"},
and the operations
@{text"+"}, @{text"-"}, @{term min} and @{term max}. 
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
is not proved even by @{text arith} because the proof relies 
on properties of multiplication.

\begin{warn}
  The running time of @{text arith} is exponential in the number of occurrences
  of \ttindexboldpos{-}{$HOL2arithfun}, \cdx{min} and
  \cdx{max} because they are first eliminated by case distinctions.

  Even for linear arithmetic formulae, \isa{arith} is incomplete. If divisibility plays a
  role, it may fail to prove a valid formula, for example
  @{prop"m+m \<noteq> n+n+1"}. Fortunately, such examples are rare.
\end{warn}
*}

(*<*)
end
(*>*)
