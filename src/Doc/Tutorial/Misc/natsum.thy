(*<*)
theory natsum imports Main begin
(*>*)
text\<open>\noindent
In particular, there are \<open>case\<close>-expressions, for example
@{term[display]"case n of 0 => 0 | Suc m => m"}
primitive recursion, for example
\<close>

primrec sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = Suc n + sum n"

text\<open>\noindent
and induction, for example
\<close>

lemma "sum n + sum n = n*(Suc n)"
apply(induct_tac n)
apply(auto)
done

text\<open>\newcommand{\mystar}{*%
}
\index{arithmetic operations!for \protect\isa{nat}}%
The arithmetic operations \isadxboldpos{+}{$HOL2arithfun},
\isadxboldpos{-}{$HOL2arithfun}, \isadxboldpos{\mystar}{$HOL2arithfun},
\sdx{div}, \sdx{mod}, \cdx{min} and
\cdx{max} are predefined, as are the relations
\isadxboldpos{\isasymle}{$HOL2arithrel} and
\isadxboldpos{<}{$HOL2arithrel}. As usual, \<^prop>\<open>m-n = (0::nat)\<close> if
\<^prop>\<open>m<n\<close>. There is even a least number operation
\sdx{LEAST}\@.  For example, \<^prop>\<open>(LEAST n. 0 < n) = Suc 0\<close>.
\begin{warn}\index{overloading}
  The constants \cdx{0} and \cdx{1} and the operations
  \isadxboldpos{+}{$HOL2arithfun}, \isadxboldpos{-}{$HOL2arithfun},
  \isadxboldpos{\mystar}{$HOL2arithfun}, \cdx{min},
  \cdx{max}, \isadxboldpos{\isasymle}{$HOL2arithrel} and
  \isadxboldpos{<}{$HOL2arithrel} are overloaded: they are available
  not just for natural numbers but for other types as well.
  For example, given the goal \<open>x + 0 = x\<close>, there is nothing to indicate
  that you are talking about natural numbers. Hence Isabelle can only infer
  that \<^term>\<open>x\<close> is of some arbitrary type where \<open>0\<close> and \<open>+\<close> are
  declared. As a consequence, you will be unable to prove the
  goal. To alert you to such pitfalls, Isabelle flags numerals without a
  fixed type in its output: \<^prop>\<open>x+0 = x\<close>. (In the absence of a numeral,
  it may take you some time to realize what has happened if \pgmenu{Show
  Types} is not set).  In this particular example, you need to include
  an explicit type constraint, for example \<open>x+0 = (x::nat)\<close>. If there
  is enough contextual information this may not be necessary: \<^prop>\<open>Suc x =
  x\<close> automatically implies \<open>x::nat\<close> because \<^term>\<open>Suc\<close> is not
  overloaded.

  For details on overloading see \S\ref{sec:overloading}.
  Table~\ref{tab:overloading} in the appendix shows the most important
  overloaded operations.
\end{warn}
\begin{warn}
  The symbols \isadxboldpos{>}{$HOL2arithrel} and
  \isadxboldpos{\isasymge}{$HOL2arithrel} are merely syntax: \<open>x > y\<close>
  stands for \<^prop>\<open>y < x\<close> and similary for \<open>\<ge>\<close> and
  \<open>\<le>\<close>.
\end{warn}
\begin{warn}
  Constant \<open>1::nat\<close> is defined to equal \<^term>\<open>Suc 0\<close>. This definition
  (see \S\ref{sec:ConstDefinitions}) is unfolded automatically by some
  tactics (like \<open>auto\<close>, \<open>simp\<close> and \<open>arith\<close>) but not by
  others (especially the single step tactics in Chapter~\ref{chap:rules}).
  If you need the full set of numerals, see~\S\ref{sec:numerals}.
  \emph{Novices are advised to stick to \<^term>\<open>0::nat\<close> and \<^term>\<open>Suc\<close>.}
\end{warn}

Both \<open>auto\<close> and \<open>simp\<close>
(a method introduced below, \S\ref{sec:Simplification}) prove 
simple arithmetic goals automatically:
\<close>

lemma "\<lbrakk> \<not> m < n; m < n + (1::nat) \<rbrakk> \<Longrightarrow> m = n"
(*<*)by(auto)(*>*)

text\<open>\noindent
For efficiency's sake, this built-in prover ignores quantified formulae,
many logical connectives, and all arithmetic operations apart from addition.
In consequence, \<open>auto\<close> and \<open>simp\<close> cannot prove this slightly more complex goal:
\<close>

lemma "m \<noteq> (n::nat) \<Longrightarrow> m < n \<or> n < m"
(*<*)by(arith)(*>*)

text\<open>\noindent The method \methdx{arith} is more general.  It attempts to
prove the first subgoal provided it is a \textbf{linear arithmetic} formula.
Such formulas may involve the usual logical connectives (\<open>\<not>\<close>,
\<open>\<and>\<close>, \<open>\<or>\<close>, \<open>\<longrightarrow>\<close>, \<open>=\<close>,
\<open>\<forall>\<close>, \<open>\<exists>\<close>), the relations \<open>=\<close>,
\<open>\<le>\<close> and \<open><\<close>, and the operations \<open>+\<close>, \<open>-\<close>,
\<^term>\<open>min\<close> and \<^term>\<open>max\<close>.  For example,\<close>

lemma "min i (max j (k*k)) = max (min (k*k) i) (min i (j::nat))"
apply(arith)
(*<*)done(*>*)

text\<open>\noindent
succeeds because \<^term>\<open>k*k\<close> can be treated as atomic. In contrast,
\<close>

lemma "n*n = n+1 \<Longrightarrow> n=0"
(*<*)oops(*>*)

text\<open>\noindent
is not proved by \<open>arith\<close> because the proof relies 
on properties of multiplication. Only multiplication by numerals (which is
the same as iterated addition) is taken into account.

\begin{warn} The running time of \<open>arith\<close> is exponential in the number
  of occurrences of \ttindexboldpos{-}{$HOL2arithfun}, \cdx{min} and
  \cdx{max} because they are first eliminated by case distinctions.

If \<open>k\<close> is a numeral, \sdx{div}~\<open>k\<close>, \sdx{mod}~\<open>k\<close> and
\<open>k\<close>~\sdx{dvd} are also supported, where the former two are eliminated
by case distinctions, again blowing up the running time.

If the formula involves quantifiers, \<open>arith\<close> may take
super-exponential time and space.
\end{warn}
\<close>

(*<*)
end
(*>*)
