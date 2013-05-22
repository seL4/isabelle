(* Author: Tobias Nipkow *)

theory Hoare_Examples imports Hoare begin

text{* Summing up the first @{text x} natural numbers in variable @{text y}. *}

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');; ''x'' ::= Plus (V ''x'') (N -1))"

text{* For this example we make use of some predefined functions.  Function
@{const Setsum}, also written @{text"\<Sum>"}, sums up the elements of a set. The
set of numbers from @{text m} to @{text n} is written @{term "{m .. n}"}. *}

subsubsection{* Proof by Operational Semantics *}

text{* The behaviour of the loop is proved by induction: *}

lemma set_ivl_lemma:
  "i \<le> j \<Longrightarrow> {i..j} = insert j {i..j - (1::int)}"
apply(simp add:atLeastAtMost_def atLeast_def atMost_def del: simp_from_to)
apply(fastforce)
done

lemma while_sum:
  "(wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = s ''y'' + \<Sum> {1 .. s ''x''}"
apply(induction wsum s t rule: big_step_induct)
apply(auto simp add: set_ivl_lemma)
done

text{* We were lucky that the proof was practically automatic, except for the
induction. In general, such proofs will not be so easy. The automation is
partly due to the right inversion rules that we set up as automatic
elimination rules that decompose big-step premises.

Now we prefix the loop with the necessary initialization: *}

lemma sum_via_bigstep:
assumes "(''y'' ::= N 0;; wsum, s) \<Rightarrow> t"
shows "t ''y'' = \<Sum> {1 .. s ''x''}"
proof -
  from assms have "(wsum,s(''y'':=0)) \<Rightarrow> t" by auto
  from while_sum[OF this] show ?thesis by simp
qed


subsubsection{* Proof by Hoare Logic *}

text{* Note that we deal with sequences of commands from right to left,
pulling back the postcondition towards the precondition. *}

lemma "\<turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = \<Sum> {1 .. n}}"
apply(rule hoare.Seq)
prefer 2
apply(rule While' [where P = "\<lambda>s. (s ''y'' = \<Sum> {1..n} - \<Sum> {1 .. s ''x''})"])
apply(rule Seq)
prefer 2
apply(rule Assign)
apply(rule Assign')
apply simp
apply(simp add: algebra_simps set_ivl_lemma minus_numeral_simps(1)[symmetric]
  del: minus_numeral_simps)
apply(simp)
apply(rule Assign')
apply simp
done

text{* The proof is intentionally an apply skript because it merely composes
the rules of Hoare logic. Of course, in a few places side conditions have to
be proved. But since those proofs are 1-liners, a structured proof is
overkill. In fact, we shall learn later that the application of the Hoare
rules can be automated completely and all that is left for the user is to
provide the loop invariants and prove the side-conditions. *}

end
