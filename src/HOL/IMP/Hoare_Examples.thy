(* Author: Tobias Nipkow *)

theory Hoare_Examples imports Hoare begin

subsection{* Example: Sums *}

text{* Summing up the first @{text n} natural numbers. The sum is accumulated
in variable @{text 0}, the loop counter is variable @{text 1}. *}

abbreviation "w n ==
  WHILE Less (V ''y'') (N n)
  DO ( ''y'' ::= Plus (V ''y'') (N 1); ''x'' ::= Plus (V ''x'') (V ''y'') )"

text{* For this example we make use of some predefined functions.  Function
@{const Setsum}, also written @{text"\<Sum>"}, sums up the elements of a set. The
set of numbers from @{text m} to @{text n} is written @{term "{m .. n}"}. *}

subsubsection{* Proof by Operational Semantics *}

text{* The behaviour of the loop is proved by induction: *}

lemma setsum_head_plus_1:
  "m \<le> n \<Longrightarrow> setsum f {m..n} = f m + setsum f {m+1..n::int}"
by (subst simp_from_to) simp
  
lemma while_sum:
  "(w n, s) \<Rightarrow> t \<Longrightarrow> t ''x'' = s ''x'' + \<Sum> {s ''y'' + 1 .. n}"
apply(induction "w n" s t rule: big_step_induct)
apply(auto simp add: setsum_head_plus_1)
done

text{* We were lucky that the proof was practically automatic, except for the
induction. In general, such proofs will not be so easy. The automation is
partly due to the right inversion rules that we set up as automatic
elimination rules that decompose big-step premises.

Now we prefix the loop with the necessary initialization: *}

lemma sum_via_bigstep:
assumes "(''x'' ::= N 0; ''y'' ::= N 0; w n, s) \<Rightarrow> t"
shows "t ''x'' = \<Sum> {1 .. n}"
proof -
  from assms have "(w n,s(''x'':=0,''y'':=0)) \<Rightarrow> t" by auto
  from while_sum[OF this] show ?thesis by simp
qed


subsubsection{* Proof by Hoare Logic *}

text{* Note that we deal with sequences of commands from right to left,
pulling back the postcondition towards the precondition. *}

lemma "\<turnstile> {\<lambda>s. 0 <= n} ''x'' ::= N 0; ''y'' ::= N 0; w n {\<lambda>s. s ''x'' = \<Sum> {1 .. n}}"
apply(rule hoare.Seq)
prefer 2
apply(rule While'
  [where P = "\<lambda>s. s ''x'' = \<Sum> {1..s ''y''} \<and> 0 \<le> s ''y'' \<and> s ''y'' \<le> n"])
apply(rule Seq)
prefer 2
apply(rule Assign)
apply(rule Assign')
apply(fastforce simp: atLeastAtMostPlus1_int_conv algebra_simps)
apply(fastforce)
apply(rule Seq)
prefer 2
apply(rule Assign)
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
