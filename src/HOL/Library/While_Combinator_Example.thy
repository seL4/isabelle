header {* \title{} *}

theory While_Combinator_Example = While_Combinator:

text {*
 \medskip An application: computation of the @{term lfp} on finite
 sets via iteration.
*}

theorem lfp_conv_while:
  "mono f ==> finite U ==> f U = U ==>
    lfp f = fst (while (\<lambda>(A, fA). A \<noteq> fA) (\<lambda>(A, fA). (fA, f fA)) ({}, f {}))"
apply (rule_tac P = "\<lambda>(A, B). (A \<subseteq> U \<and> B = f A \<and> A \<subseteq> B \<and> B \<subseteq> lfp f)" and
                r = "((Pow U <*> UNIV) <*> (Pow U <*> UNIV)) \<inter>
                     inv_image finite_psubset (op - U o fst)" in while_rule)
   apply (subst lfp_unfold)
    apply assumption
   apply (simp add: monoD)
  apply (subst lfp_unfold)
   apply assumption
  apply clarsimp
  apply (blast dest: monoD)
 apply (fastsimp intro!: lfp_lowerbound)
 apply (blast intro: wf_finite_psubset Int_lower2 [THEN [2] wf_subset])
apply (clarsimp simp add: inv_image_def finite_psubset_def order_less_le)
apply (blast intro!: finite_Diff dest: monoD)
done

text {*
 An example of using the @{term while} combinator.
*}

lemma aux: "{f n | n. A n \<or> B n} = {f n | n. A n} \<union> {f n | n. B n}"
  apply blast
  done

theorem "P (lfp (\<lambda>N::int set. {#0} \<union> {(n + #2) mod #6 | n. n \<in> N})) =
    P {#0, #4, #2}"
  apply (subst lfp_conv_while [where ?U = "{#0, #1, #2, #3, #4, #5}"])
     apply (rule monoI)
    apply blast
   apply simp
  apply (simp add: aux set_eq_subset)
  txt {* The fixpoint computation is performed purely by rewriting: *}
  apply (simp add: while_unfold aux set_eq_subset del: subset_empty)
  done

end
