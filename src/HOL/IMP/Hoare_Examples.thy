(* Author: Tobias Nipkow *)

theory Hoare_Examples imports Hoare begin

text{* The following lemmas improve proof automation and should be included
(globally?) when dealing with negative numerals. *}

lemma add_neg1R[simp]:
  "x + -1 = x - (1 :: 'a :: neg_numeral)"
unfolding minus_one[symmetric] by (rule diff_minus[symmetric])
lemma add_neg1L[simp]:
  "-1 + x = x - (1 :: 'a :: {neg_numeral, ab_group_add})"
unfolding minus_one[symmetric] by simp

lemma add_neg_numeralL[simp]:
  "x + neg_numeral n = (x::'a::neg_numeral) - numeral(n)"
by (simp only: diff_minus_eq_add[symmetric] minus_neg_numeral)
lemma add_neg_numeralR[simp]:
  "neg_numeral n + x = (x::'a::{neg_numeral,ab_group_add}) - numeral(n)"
by simp


text{* Summing up the first @{text x} natural numbers in variable @{text y}. *}

fun sum :: "int \<Rightarrow> int" where
"sum i = (if i <= 0 then 0 else sum (i - 1) + i)"

lemma [simp]: "0 < i \<Longrightarrow> sum i = sum (i - 1) + i" "i <= 0 \<Longrightarrow> sum i = 0"
by(simp_all)

declare sum.simps[simp del]

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'')
  DO (''y'' ::= Plus (V ''y'') (V ''x'');; ''x'' ::= Plus (V ''x'') (N -1))"


subsubsection{* Proof by Operational Semantics *}

text{* The behaviour of the loop is proved by induction: *}

lemma while_sum:
  "(wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = s ''y'' + sum(s ''x'')"
apply(induction wsum s t rule: big_step_induct)
apply(auto)
done

text{* We were lucky that the proof was automatic, except for the
induction. In general, such proofs will not be so easy. The automation is
partly due to the right inversion rules that we set up as automatic
elimination rules that decompose big-step premises.

Now we prefix the loop with the necessary initialization: *}

lemma sum_via_bigstep:
  assumes "(''y'' ::= N 0;; wsum, s) \<Rightarrow> t"
  shows "t ''y'' = sum (s ''x'')"
proof -
  from assms have "(wsum,s(''y'':=0)) \<Rightarrow> t" by auto
  from while_sum[OF this] show ?thesis by simp
qed


subsubsection{* Proof by Hoare Logic *}

text{* Note that we deal with sequences of commands from right to left,
pulling back the postcondition towards the precondition. *}

lemma "\<turnstile> {\<lambda>s. s ''x'' = n} ''y'' ::= N 0;; wsum {\<lambda>s. s ''y'' = sum n}"
apply(rule Seq)
 prefer 2
 apply(rule While' [where P = "\<lambda>s. (s ''y'' = sum n - sum(s ''x''))"])
  apply(rule Seq)
   prefer 2
   apply(rule Assign)
  apply(rule Assign')
  apply simp
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
