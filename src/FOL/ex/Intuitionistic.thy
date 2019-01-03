(*  Title:      FOL/ex/Intuitionistic.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section \<open>Intuitionistic First-Order Logic\<close>

theory Intuitionistic
imports IFOL
begin

(*
Single-step ML commands:
by (IntPr.step_tac 1)
by (biresolve_tac safe_brls 1);
by (biresolve_tac haz_brls 1);
by (assume_tac 1);
by (IntPr.safe_tac 1);
by (IntPr.mp_tac 1);
by (IntPr.fast_tac @{context} 1);
*)


text\<open>Metatheorem (for \emph{propositional} formulae):
  $P$ is classically provable iff $\neg\neg P$ is intuitionistically provable.
  Therefore $\neg P$ is classically provable iff it is intuitionistically
  provable.

Proof: Let $Q$ be the conjuction of the propositions $A\vee\neg A$, one for
each atom $A$ in $P$.  Now $\neg\neg Q$ is intuitionistically provable because
$\neg\neg(A\vee\neg A)$ is and because double-negation distributes over
conjunction.  If $P$ is provable classically, then clearly $Q\rightarrow P$ is
provable intuitionistically, so $\neg\neg(Q\rightarrow P)$ is also provable
intuitionistically.  The latter is intuitionistically equivalent to $\neg\neg
Q\rightarrow\neg\neg P$, hence to $\neg\neg P$, since $\neg\neg Q$ is
intuitionistically provable.  Finally, if $P$ is a negation then $\neg\neg P$
is intuitionstically equivalent to $P$.  [Andy Pitts]\<close>

lemma \<open>\<not> \<not> (P \<and> Q) \<longleftrightarrow> \<not> \<not> P \<and> \<not> \<not> Q\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>\<not> \<not> ((\<not> P \<longrightarrow> Q) \<longrightarrow> (\<not> P \<longrightarrow> \<not> Q) \<longrightarrow> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text \<open>Double-negation does NOT distribute over disjunction.\<close>

lemma \<open>\<not> \<not> (P \<longrightarrow> Q) \<longleftrightarrow> (\<not> \<not> P \<longrightarrow> \<not> \<not> Q)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>\<not> \<not> \<not> P \<longleftrightarrow> \<not> P\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>\<not> \<not> ((P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longrightarrow> Q) \<or> (P \<longrightarrow> R))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>(P \<longleftrightarrow> Q) \<longleftrightarrow> (Q \<longleftrightarrow> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>((P \<longrightarrow> (Q \<or> (Q \<longrightarrow> R))) \<longrightarrow> R) \<longrightarrow> R\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma
  \<open>(((G \<longrightarrow> A) \<longrightarrow> J) \<longrightarrow> D \<longrightarrow> E) \<longrightarrow> (((H \<longrightarrow> B) \<longrightarrow> I) \<longrightarrow> C \<longrightarrow> J)
    \<longrightarrow> (A \<longrightarrow> H) \<longrightarrow> F \<longrightarrow> G \<longrightarrow> (((C \<longrightarrow> B) \<longrightarrow> I) \<longrightarrow> D) \<longrightarrow> (A \<longrightarrow> C)
    \<longrightarrow> (((F \<longrightarrow> A) \<longrightarrow> B) \<longrightarrow> I) \<longrightarrow> E\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


subsection \<open>Lemmas for the propositional double-negation translation\<close>

lemma \<open>P \<longrightarrow> \<not> \<not> P\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>\<not> \<not> (\<not> \<not> P \<longrightarrow> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>\<not> \<not> P \<and> \<not> \<not> (P \<longrightarrow> Q) \<longrightarrow> \<not> \<not> Q\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


text \<open>The following are classically but not constructively valid.
  The attempt to prove them terminates quickly!\<close>
lemma \<open>((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P\<close>
apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
oops

lemma \<open>(P \<and> Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> R) \<or> (Q \<longrightarrow> R)\<close>
apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
oops


subsection \<open>de Bruijn formulae\<close>

text \<open>de Bruijn formula with three predicates\<close>
lemma
  \<open>((P \<longleftrightarrow> Q) \<longrightarrow> P \<and> Q \<and> R) \<and>
    ((Q \<longleftrightarrow> R) \<longrightarrow> P \<and> Q \<and> R) \<and>
    ((R \<longleftrightarrow> P) \<longrightarrow> P \<and> Q \<and> R) \<longrightarrow> P \<and> Q \<and> R\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


text \<open>de Bruijn formula with five predicates\<close>
lemma
  \<open>((P \<longleftrightarrow> Q) \<longrightarrow> P \<and> Q \<and> R \<and> S \<and> T) \<and>
    ((Q \<longleftrightarrow> R) \<longrightarrow> P \<and> Q \<and> R \<and> S \<and> T) \<and>
    ((R \<longleftrightarrow> S) \<longrightarrow> P \<and> Q \<and> R \<and> S \<and> T) \<and>
    ((S \<longleftrightarrow> T) \<longrightarrow> P \<and> Q \<and> R \<and> S \<and> T) \<and>
    ((T \<longleftrightarrow> P) \<longrightarrow> P \<and> Q \<and> R \<and> S \<and> T) \<longrightarrow> P \<and> Q \<and> R \<and> S \<and> T\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


text \<open>
  Problems from of Sahlin, Franzen and Haridi,
  An Intuitionistic Predicate Logic Theorem Prover.
  J. Logic and Comp. 2 (5), October 1992, 619-656.
\<close>

text\<open>Problem 1.1\<close>
lemma
  \<open>(\<forall>x. \<exists>y. \<forall>z. p(x) \<and> q(y) \<and> r(z)) \<longleftrightarrow>
    (\<forall>z. \<exists>y. \<forall>x. p(x) \<and> q(y) \<and> r(z))\<close>
  by (tactic \<open>IntPr.best_dup_tac @{context} 1\<close>)  \<comment> \<open>SLOW\<close>

text\<open>Problem 3.1\<close>
lemma \<open>\<not> (\<exists>x. \<forall>y. mem(y,x) \<longleftrightarrow> \<not> mem(x,x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>Problem 4.1: hopeless!\<close>
lemma
  \<open>(\<forall>x. p(x) \<longrightarrow> p(h(x)) \<or> p(g(x))) \<and> (\<exists>x. p(x)) \<and> (\<forall>x. \<not> p(h(x)))
    \<longrightarrow> (\<exists>x. p(g(g(g(g(g(x)))))))\<close>
  oops


subsection \<open>Intuitionistic FOL: propositional problems based on Pelletier.\<close>

text\<open>\<open>\<not>\<not>\<close>1\<close>
lemma \<open>\<not> \<not> ((P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> \<not> P))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>2\<close>
lemma \<open>\<not> \<not> (\<not> \<not> P \<longleftrightarrow> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>3\<close>
lemma \<open>\<not> (P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>4\<close>
lemma \<open>\<not> \<not> ((\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>5\<close>
lemma \<open>\<not> \<not> ((P \<or> Q \<longrightarrow> P \<or> R) \<longrightarrow> P \<or> (Q \<longrightarrow> R))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>6\<close>
lemma \<open>\<not> \<not> (P \<or> \<not> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>7\<close>
lemma \<open>\<not> \<not> (P \<or> \<not> \<not> \<not> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>8. Peirce's law\<close>
lemma \<open>\<not> \<not> (((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>9\<close>
lemma \<open>((P \<or> Q) \<and> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)) \<longrightarrow> \<not> (\<not> P \<or> \<not> Q)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>10\<close>
lemma \<open>(Q \<longrightarrow> R) \<longrightarrow> (R \<longrightarrow> P \<and> Q) \<longrightarrow> (P \<longrightarrow> (Q \<or> R)) \<longrightarrow> (P \<longleftrightarrow> Q)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


subsection\<open>11. Proved in each direction (incorrectly, says Pelletier!!)\<close>

lemma \<open>P \<longleftrightarrow> P\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>12. Dijkstra's law\<close>
lemma \<open>\<not> \<not> (((P \<longleftrightarrow> Q) \<longleftrightarrow> R) \<longleftrightarrow> (P \<longleftrightarrow> (Q \<longleftrightarrow> R)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>((P \<longleftrightarrow> Q) \<longleftrightarrow> R) \<longrightarrow> \<not> \<not> (P \<longleftrightarrow> (Q \<longleftrightarrow> R))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>13. Distributive law\<close>
lemma \<open>P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>14\<close>
lemma \<open>\<not> \<not> ((P \<longleftrightarrow> Q) \<longleftrightarrow> ((Q \<or> \<not> P) \<and> (\<not> Q \<or> P)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>15\<close>
lemma \<open>\<not> \<not> ((P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>16\<close>
lemma \<open>\<not> \<not> ((P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>17\<close>
lemma \<open>\<not> \<not> (((P \<and> (Q \<longrightarrow> R)) \<longrightarrow> S) \<longleftrightarrow> ((\<not> P \<or> Q \<or> S) \<and> (\<not> P \<or> \<not> R \<or> S)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text \<open>Dijkstra's ``Golden Rule''\<close>
lemma \<open>(P \<and> Q) \<longleftrightarrow> P \<longleftrightarrow> Q \<longleftrightarrow> (P \<or> Q)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


section \<open>Examples with quantifiers\<close>

subsection \<open>The converse is classical in the following implications \dots\<close>

lemma \<open>(\<exists>x. P(x) \<longrightarrow> Q) \<longrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>((\<forall>x. P(x)) \<longrightarrow> Q) \<longrightarrow> \<not> (\<forall>x. P(x) \<and> \<not> Q)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>((\<forall>x. \<not> P(x)) \<longrightarrow> Q) \<longrightarrow> \<not> (\<forall>x. \<not> (P(x) \<or> Q))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>(\<forall>x. P(x)) \<or> Q \<longrightarrow> (\<forall>x. P(x) \<or> Q)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

lemma \<open>(\<exists>x. P \<longrightarrow> Q(x)) \<longrightarrow> (P \<longrightarrow> (\<exists>x. Q(x)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)


subsection \<open>The following are not constructively valid!\<close>
text \<open>The attempt to prove them terminates quickly!\<close>

lemma \<open>((\<forall>x. P(x)) \<longrightarrow> Q) \<longrightarrow> (\<exists>x. P(x) \<longrightarrow> Q)\<close>
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
  oops

lemma \<open>(P \<longrightarrow> (\<exists>x. Q(x))) \<longrightarrow> (\<exists>x. P \<longrightarrow> Q(x))\<close>
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
  oops

lemma \<open>(\<forall>x. P(x) \<or> Q) \<longrightarrow> ((\<forall>x. P(x)) \<or> Q)\<close>
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
  oops

lemma \<open>(\<forall>x. \<not> \<not> P(x)) \<longrightarrow> \<not> \<not> (\<forall>x. P(x))\<close>
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
  oops

text \<open>Classically but not intuitionistically valid.  Proved by a bug in 1986!\<close>
lemma \<open>\<exists>x. Q(x) \<longrightarrow> (\<forall>x. Q(x))\<close>
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)?
  apply (rule asm_rl) \<comment> \<open>Checks that subgoals remain: proof failed.\<close>
  oops


subsection \<open>Hard examples with quantifiers\<close>

text \<open>
  The ones that have not been proved are not known to be valid! Some will
  require quantifier duplication -- not currently available.
\<close>

text\<open>\<open>\<not>\<not>\<close>18\<close>
lemma \<open>\<not> \<not> (\<exists>y. \<forall>x. P(y) \<longrightarrow> P(x))\<close>
  oops  \<comment> \<open>NOT PROVED\<close>

text\<open>\<open>\<not>\<not>\<close>19\<close>
lemma \<open>\<not> \<not> (\<exists>x. \<forall>y z. (P(y) \<longrightarrow> Q(z)) \<longrightarrow> (P(x) \<longrightarrow> Q(x)))\<close>
  oops  \<comment> \<open>NOT PROVED\<close>

text\<open>20\<close>
lemma
  \<open>(\<forall>x y. \<exists>z. \<forall>w. (P(x) \<and> Q(y) \<longrightarrow> R(z) \<and> S(w)))
    \<longrightarrow> (\<exists>x y. P(x) \<and> Q(y)) \<longrightarrow> (\<exists>z. R(z))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>21\<close>
lemma \<open>(\<exists>x. P \<longrightarrow> Q(x)) \<and> (\<exists>x. Q(x) \<longrightarrow> P) \<longrightarrow> \<not> \<not> (\<exists>x. P \<longleftrightarrow> Q(x))\<close>
  oops \<comment> \<open>NOT PROVED; needs quantifier duplication\<close>

text\<open>22\<close>
lemma \<open>(\<forall>x. P \<longleftrightarrow> Q(x)) \<longrightarrow> (P \<longleftrightarrow> (\<forall>x. Q(x)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>23\<close>
lemma \<open>\<not> \<not> ((\<forall>x. P \<or> Q(x)) \<longleftrightarrow> (P \<or> (\<forall>x. Q(x))))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>24\<close>
lemma
  \<open>\<not> (\<exists>x. S(x) \<and> Q(x)) \<and> (\<forall>x. P(x) \<longrightarrow> Q(x) \<or> R(x)) \<and>
    (\<not> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))) \<and> (\<forall>x. Q(x) \<or> R(x) \<longrightarrow> S(x))
    \<longrightarrow> \<not> \<not> (\<exists>x. P(x) \<and> R(x))\<close>
text \<open>
  Not clear why \<open>fast_tac\<close>, \<open>best_tac\<close>, \<open>ASTAR\<close> and
  \<open>ITER_DEEPEN\<close> all take forever.
\<close>
  apply (tactic \<open>IntPr.safe_tac @{context}\<close>)
  apply (erule impE)
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)
  apply (tactic \<open>IntPr.fast_tac @{context} 1\<close>)
  done

text\<open>25\<close>
lemma
  \<open>(\<exists>x. P(x)) \<and>
      (\<forall>x. L(x) \<longrightarrow> \<not> (M(x) \<and> R(x))) \<and>
      (\<forall>x. P(x) \<longrightarrow> (M(x) \<and> L(x))) \<and>
      ((\<forall>x. P(x) \<longrightarrow> Q(x)) \<or> (\<exists>x. P(x) \<and> R(x)))
    \<longrightarrow> (\<exists>x. Q(x) \<and> P(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>26\<close>
lemma
  \<open>(\<not> \<not> (\<exists>x. p(x)) \<longleftrightarrow> \<not> \<not> (\<exists>x. q(x))) \<and>
    (\<forall>x. \<forall>y. p(x) \<and> q(y) \<longrightarrow> (r(x) \<longleftrightarrow> s(y)))
  \<longrightarrow> ((\<forall>x. p(x) \<longrightarrow> r(x)) \<longleftrightarrow> (\<forall>x. q(x) \<longrightarrow> s(x)))\<close>
  oops  \<comment> \<open>NOT PROVED\<close>

text\<open>27\<close>
lemma
  \<open>(\<exists>x. P(x) \<and> \<not> Q(x)) \<and>
    (\<forall>x. P(x) \<longrightarrow> R(x)) \<and>
    (\<forall>x. M(x) \<and> L(x) \<longrightarrow> P(x)) \<and>
    ((\<exists>x. R(x) \<and> \<not> Q(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> \<not> R(x)))
  \<longrightarrow> (\<forall>x. M(x) \<longrightarrow> \<not> L(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>28. AMENDED\<close>
lemma
  \<open>(\<forall>x. P(x) \<longrightarrow> (\<forall>x. Q(x))) \<and>
      (\<not> \<not> (\<forall>x. Q(x) \<or> R(x)) \<longrightarrow> (\<exists>x. Q(x) \<and> S(x))) \<and>
      (\<not> \<not> (\<exists>x. S(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> M(x)))
    \<longrightarrow> (\<forall>x. P(x) \<and> L(x) \<longrightarrow> M(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>29. Essentially the same as Principia Mathematica *11.71\<close>
lemma
  \<open>(\<exists>x. P(x)) \<and> (\<exists>y. Q(y))
    \<longrightarrow> ((\<forall>x. P(x) \<longrightarrow> R(x)) \<and> (\<forall>y. Q(y) \<longrightarrow> S(y)) \<longleftrightarrow>
      (\<forall>x y. P(x) \<and> Q(y) \<longrightarrow> R(x) \<and> S(y)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>30\<close>
lemma
  \<open>(\<forall>x. (P(x) \<or> Q(x)) \<longrightarrow> \<not> R(x)) \<and>
      (\<forall>x. (Q(x) \<longrightarrow> \<not> S(x)) \<longrightarrow> P(x) \<and> R(x))
    \<longrightarrow> (\<forall>x. \<not> \<not> S(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>31\<close>
lemma
  \<open>\<not> (\<exists>x. P(x) \<and> (Q(x) \<or> R(x))) \<and>
      (\<exists>x. L(x) \<and> P(x)) \<and>
      (\<forall>x. \<not> R(x) \<longrightarrow> M(x))
  \<longrightarrow> (\<exists>x. L(x) \<and> M(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>32\<close>
lemma
  \<open>(\<forall>x. P(x) \<and> (Q(x) \<or> R(x)) \<longrightarrow> S(x)) \<and>
    (\<forall>x. S(x) \<and> R(x) \<longrightarrow> L(x)) \<and>
    (\<forall>x. M(x) \<longrightarrow> R(x))
  \<longrightarrow> (\<forall>x. P(x) \<and> M(x) \<longrightarrow> L(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>\<open>\<not>\<not>\<close>33\<close>
lemma
  \<open>(\<forall>x. \<not> \<not> (P(a) \<and> (P(x) \<longrightarrow> P(b)) \<longrightarrow> P(c))) \<longleftrightarrow>
    (\<forall>x. \<not> \<not> ((\<not> P(a) \<or> P(x) \<or> P(c)) \<and> (\<not> P(a) \<or> \<not> P(b) \<or> P(c))))\<close>
  apply (tactic \<open>IntPr.best_tac @{context} 1\<close>)
  done


text\<open>36\<close>
lemma
  \<open>(\<forall>x. \<exists>y. J(x,y)) \<and>
    (\<forall>x. \<exists>y. G(x,y)) \<and>
    (\<forall>x y. J(x,y) \<or> G(x,y) \<longrightarrow> (\<forall>z. J(y,z) \<or> G(y,z) \<longrightarrow> H(x,z)))
  \<longrightarrow> (\<forall>x. \<exists>y. H(x,y))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>37\<close>
lemma
  \<open>(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
      \<not> \<not> (P(x,z) \<longrightarrow> P(y,w)) \<and> P(y,z) \<and> (P(y,w) \<longrightarrow> (\<exists>u. Q(u,w)))) \<and>
        (\<forall>x z. \<not> P(x,z) \<longrightarrow> (\<exists>y. Q(y,z))) \<and>
        (\<not> \<not> (\<exists>x y. Q(x,y)) \<longrightarrow> (\<forall>x. R(x,x)))
    \<longrightarrow> \<not> \<not> (\<forall>x. \<exists>y. R(x,y))\<close>
  oops  \<comment> \<open>NOT PROVED\<close>

text\<open>39\<close>
lemma \<open>\<not> (\<exists>x. \<forall>y. F(y,x) \<longleftrightarrow> \<not> F(y,y))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>40. AMENDED\<close>
lemma
  \<open>(\<exists>y. \<forall>x. F(x,y) \<longleftrightarrow> F(x,x)) \<longrightarrow>
    \<not> (\<forall>x. \<exists>y. \<forall>z. F(z,y) \<longleftrightarrow> \<not> F(z,x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>44\<close>
lemma
  \<open>(\<forall>x. f(x) \<longrightarrow>
    (\<exists>y. g(y) \<and> h(x,y) \<and> (\<exists>y. g(y) \<and> \<not> h(x,y)))) \<and>
    (\<exists>x. j(x) \<and> (\<forall>y. g(y) \<longrightarrow> h(x,y)))
    \<longrightarrow> (\<exists>x. j(x) \<and> \<not> f(x))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>48\<close>
lemma \<open>(a = b \<or> c = d) \<and> (a = c \<or> b = d) \<longrightarrow> a = d \<or> b = c\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>51\<close>
lemma
  \<open>(\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
    (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P(x,y) \<longleftrightarrow> y = w) \<longleftrightarrow> x = z)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>52\<close>
text \<open>Almost the same as 51.\<close>
lemma
  \<open>(\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
    (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P(x,y) \<longleftrightarrow> x = z) \<longleftrightarrow> y = w)\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>56\<close>
lemma \<open>(\<forall>x. (\<exists>y. P(y) \<and> x = f(y)) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x. P(x) \<longrightarrow> P(f(x)))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>57\<close>
lemma
  \<open>P(f(a,b), f(b,c)) \<and> P(f(b,c), f(a,c)) \<and>
    (\<forall>x y z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<longrightarrow> P(f(a,b), f(a,c))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

text\<open>60\<close>
lemma \<open>\<forall>x. P(x,f(x)) \<longleftrightarrow> (\<exists>y. (\<forall>z. P(z,y) \<longrightarrow> P(z,f(x))) \<and> P(x,y))\<close>
  by (tactic \<open>IntPr.fast_tac @{context} 1\<close>)

end
