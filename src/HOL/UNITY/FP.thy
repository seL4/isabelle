(*  Title:      HOL/UNITY/FP.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

From Misra, "A Logic for Concurrent Programming", 1994
*)

section\<open>Fixed Point of a Program\<close>

theory FP imports UNITY begin

definition FP_Orig :: "'a program => 'a set" where
    "FP_Orig F == \<Union>{A. \<forall>B. F \<in> stable (A \<inter> B)}"

definition FP :: "'a program => 'a set" where
    "FP F == {s. F \<in> stable {s}}"

lemma stable_FP_Orig_Int: "F \<in> stable (FP_Orig F Int B)"
apply (simp only: FP_Orig_def stable_def Int_Union2)
apply (blast intro: constrains_UN)
done

lemma FP_Orig_weakest:
    "(\<And>B. F \<in> stable (A \<inter> B)) \<Longrightarrow> A <= FP_Orig F"
by (simp add: FP_Orig_def stable_def, blast)

lemma stable_FP_Int: "F \<in> stable (FP F \<inter> B)"
proof -
  have "F \<in> stable (\<Union>x\<in>B. FP F \<inter> {x})"
    apply (simp only: Int_insert_right FP_def stable_def)
    apply (rule constrains_UN)
    apply simp
    done
  also have "(\<Union>x\<in>B. FP F \<inter> {x}) = FP F \<inter> B"
    by simp
  finally show ?thesis .
qed

lemma FP_equivalence: "FP F = FP_Orig F"
apply (rule equalityI) 
 apply (rule stable_FP_Int [THEN FP_Orig_weakest])
apply (simp add: FP_Orig_def FP_def, clarify)
apply (drule_tac x = "{x}" in spec)
apply (simp add: Int_insert_right)
done

lemma FP_weakest:
    "(\<And>B. F \<in> stable (A Int B)) \<Longrightarrow> A <= FP F"
by (simp add: FP_equivalence FP_Orig_weakest)

lemma Compl_FP: 
    "-(FP F) = (UN act: Acts F. -{s. act``{s} <= {s}})"
by (simp add: FP_def stable_def constrains_def, blast)

lemma Diff_FP: "A - (FP F) = (UN act: Acts F. A - {s. act``{s} <= {s}})"
by (simp add: Diff_eq Compl_FP)

lemma totalize_FP [simp]: "FP (totalize F) = FP F"
by (simp add: FP_def)

end
