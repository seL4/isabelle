(*  Title:      HOL/ex/While_Combinator_Example.thy
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen
*)

section \<open>An application of the While combinator\<close>

theory While_Combinator_Example
imports "HOL-Library.While_Combinator"
begin

text \<open>Computation of the @{term lfp} on finite sets via 
  iteration.\<close>

theorem lfp_conv_while:
  "[| mono f; finite U; f U = U |] ==>
    lfp f = fst (while (\<lambda>(A, fA). A \<noteq> fA) (\<lambda>(A, fA). (fA, f fA)) ({}, f {}))"
apply (rule_tac P = "\<lambda>(A, B). (A \<subseteq> U \<and> B = f A \<and> A \<subseteq> B \<and> B \<subseteq> lfp f)" and
                r = "((Pow U \<times> UNIV) \<times> (Pow U \<times> UNIV)) \<inter>
                     inv_image finite_psubset ((-) U o fst)" in while_rule)
   apply (subst lfp_unfold)
    apply assumption
   apply (simp add: monoD)
  apply (subst lfp_unfold)
   apply assumption
  apply clarsimp
  apply (blast dest: monoD)
 apply (fastforce intro!: lfp_lowerbound)
 apply (blast intro: wf_finite_psubset Int_lower2 [THEN [2] wf_subset])
apply (clarsimp simp add: finite_psubset_def order_less_le)
apply (blast dest: monoD)
done


subsection \<open>Example\<close>

text\<open>Cannot use @{thm[source]set_eq_subset} because it leads to
looping because the antisymmetry simproc turns the subset relationship
back into equality.\<close>

theorem "P (lfp (\<lambda>N::int set. {0} \<union> {(n + 2) mod 6 | n. n \<in> N})) =
  P {0, 4, 2}"
proof -
  have seteq: "\<And>A B. (A = B) = ((\<forall>a \<in> A. a\<in>B) \<and> (\<forall>b\<in>B. b\<in>A))"
    by blast
  have aux: "\<And>f A B. {f n | n. A n \<or> B n} = {f n | n. A n} \<union> {f n | n. B n}"
    apply blast
    done
  show ?thesis
    apply (subst lfp_conv_while [where ?U = "{0, 1, 2, 3, 4, 5}"])
       apply (rule monoI)
      apply blast
     apply simp
    apply (simp add: aux set_eq_subset)
    txt \<open>The fixpoint computation is performed purely by rewriting:\<close>
    apply (simp add: while_unfold aux seteq del: subset_empty)
    done
qed

end
