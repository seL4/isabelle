
header {* \title{} *}

theory While_Combinator_Example = While_Combinator:

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
