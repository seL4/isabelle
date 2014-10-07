(*  Title:      HOL/Isar_Examples/Summation.thy
    Author:     Markus Wenzel
*)

header \<open>Summing natural numbers\<close>

theory Summation
imports Main
begin

text \<open>Subsequently, we prove some summation laws of natural numbers
  (including odds, squares, and cubes).  These examples demonstrate
  how plain natural deduction (including induction) may be combined
  with calculational proof.\<close>


subsection \<open>Summation laws\<close>

text \<open>The sum of natural numbers $0 + \cdots + n$ equals $n \times
  (n + 1)/2$.  Avoiding formal reasoning about division we prove this
  equation multiplied by $2$.\<close>

theorem sum_of_naturals:
  "2 * (\<Sum>i::nat=0..n. i) = n * (n + 1)"
  (is "?P n" is "?S n = _")
proof (induct n)
  show "?P 0" by simp
next
  fix n have "?S (n + 1) = ?S n + 2 * (n + 1)"
    by simp
  also assume "?S n = n * (n + 1)"
  also have "\<dots> + 2 * (n + 1) = (n + 1) * (n + 2)"
    by simp
  finally show "?P (Suc n)"
    by simp
qed

text \<open>The above proof is a typical instance of mathematical
  induction.  The main statement is viewed as some $\var{P} \ap n$
  that is split by the induction method into base case $\var{P} \ap
  0$, and step case $\var{P} \ap n \Impl \var{P} \ap (\idt{Suc} \ap
  n)$ for arbitrary $n$.

  The step case is established by a short calculation in forward
  manner.  Starting from the left-hand side $\var{S} \ap (n + 1)$ of
  the thesis, the final result is achieved by transformations
  involving basic arithmetic reasoning (using the Simplifier).  The
  main point is where the induction hypothesis $\var{S} \ap n = n
  \times (n + 1)$ is introduced in order to replace a certain subterm.
  So the ``transitivity'' rule involved here is actual
  \emph{substitution}.  Also note how the occurrence of ``\dots'' in
  the subsequent step documents the position where the right-hand side
  of the hypothesis got filled in.

  \medskip A further notable point here is integration of calculations
  with plain natural deduction.  This works so well in Isar for two
  reasons.
  \begin{enumerate}

  \item Facts involved in \isakeyword{also}~/ \isakeyword{finally}
  calculational chains may be just anything.  There is nothing special
  about \isakeyword{have}, so the natural deduction element
  \isakeyword{assume} works just as well.

  \item There are two \emph{separate} primitives for building natural
  deduction contexts: \isakeyword{fix}~$x$ and
  \isakeyword{assume}~$A$.  Thus it is possible to start reasoning
  with some new ``arbitrary, but fixed'' elements before bringing in
  the actual assumption.  In contrast, natural deduction is
  occasionally formalized with basic context elements of the form
  $x:A$ instead.

  \end{enumerate}
\<close>

text \<open>\medskip We derive further summation laws for odds, squares,
  and cubes as follows.  The basic technique of induction plus
  calculation is the same as before.\<close>

theorem sum_of_odds:
  "(\<Sum>i::nat=0..<n. 2 * i + 1) = n^Suc (Suc 0)"
  (is "?P n" is "?S n = _")
proof (induct n)
  show "?P 0" by simp
next
  fix n
  have "?S (n + 1) = ?S n + 2 * n + 1"
    by simp
  also assume "?S n = n^Suc (Suc 0)"
  also have "\<dots> + 2 * n + 1 = (n + 1)^Suc (Suc 0)"
    by simp
  finally show "?P (Suc n)"
    by simp
qed

text \<open>Subsequently we require some additional tweaking of Isabelle
  built-in arithmetic simplifications, such as bringing in
  distributivity by hand.\<close>

lemmas distrib = add_mult_distrib add_mult_distrib2

theorem sum_of_squares:
  "6 * (\<Sum>i::nat=0..n. i^Suc (Suc 0)) = n * (n + 1) * (2 * n + 1)"
  (is "?P n" is "?S n = _")
proof (induct n)
  show "?P 0" by simp
next
  fix n
  have "?S (n + 1) = ?S n + 6 * (n + 1)^Suc (Suc 0)"
    by (simp add: distrib)
  also assume "?S n = n * (n + 1) * (2 * n + 1)"
  also have "\<dots> + 6 * (n + 1)^Suc (Suc 0) =
      (n + 1) * (n + 2) * (2 * (n + 1) + 1)"
    by (simp add: distrib)
  finally show "?P (Suc n)"
    by simp
qed

theorem sum_of_cubes:
  "4 * (\<Sum>i::nat=0..n. i^3) = (n * (n + 1))^Suc (Suc 0)"
  (is "?P n" is "?S n = _")
proof (induct n)
  show "?P 0" by (simp add: power_eq_if)
next
  fix n
  have "?S (n + 1) = ?S n + 4 * (n + 1)^3"
    by (simp add: power_eq_if distrib)
  also assume "?S n = (n * (n + 1))^Suc (Suc 0)"
  also have "\<dots> + 4 * (n + 1)^3 = ((n + 1) * ((n + 1) + 1))^Suc (Suc 0)"
    by (simp add: power_eq_if distrib)
  finally show "?P (Suc n)"
    by simp
qed

text \<open>Note that in contrast to older traditions of tactical proof
  scripts, the structured proof applies induction on the original,
  unsimplified statement.  This allows to state the induction cases
  robustly and conveniently.  Simplification (or other automated)
  methods are then applied in terminal position to solve certain
  sub-problems completely.

  As a general rule of good proof style, automatic methods such as
  $\idt{simp}$ or $\idt{auto}$ should normally be never used as
  initial proof methods with a nested sub-proof to address the
  automatically produced situation, but only as terminal ones to solve
  sub-problems.\<close>

end
