(*  Title:      FOL/ex/Foundation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section "Intuitionistic FOL: Examples from The Foundation of a Generic Theorem Prover"

theory Foundation
imports IFOL
begin

lemma "A \<and> B \<longrightarrow> (C \<longrightarrow> A \<and> C)"
apply (rule impI)
apply (rule impI)
apply (rule conjI)
prefer 2 apply assumption
apply (rule conjunct1)
apply assumption
done

text \<open>A form of conj-elimination\<close>
lemma
  assumes "A \<and> B"
    and "A \<Longrightarrow> B \<Longrightarrow> C"
  shows C
apply (rule assms)
apply (rule conjunct1)
apply (rule assms)
apply (rule conjunct2)
apply (rule assms)
done

lemma
  assumes "\<And>A. \<not> \<not> A \<Longrightarrow> A"
  shows "B \<or> \<not> B"
apply (rule assms)
apply (rule notI)
apply (rule_tac P = "\<not> B" in notE)
apply (rule_tac [2] notI)
apply (rule_tac [2] P = "B \<or> \<not> B" in notE)
prefer 2 apply assumption
apply (rule_tac [2] disjI1)
prefer 2 apply assumption
apply (rule notI)
apply (rule_tac P = "B \<or> \<not> B" in notE)
apply assumption
apply (rule disjI2)
apply assumption
done

lemma
  assumes "\<And>A. \<not> \<not> A \<Longrightarrow> A"
  shows "B \<or> \<not> B"
apply (rule assms)
apply (rule notI)
apply (rule notE)
apply (rule_tac [2] notI)
apply (erule_tac [2] notE)
apply (erule_tac [2] disjI1)
apply (rule notI)
apply (erule notE)
apply (erule disjI2)
done


lemma
  assumes "A \<or> \<not> A"
    and "\<not> \<not> A"
  shows A
apply (rule disjE)
apply (rule assms)
apply assumption
apply (rule FalseE)
apply (rule_tac P = "\<not> A" in notE)
apply (rule assms)
apply assumption
done


subsection "Examples with quantifiers"

lemma
  assumes "\<forall>z. G(z)"
  shows "\<forall>z. G(z) \<or> H(z)"
apply (rule allI)
apply (rule disjI1)
apply (rule assms [THEN spec])
done

lemma "\<forall>x. \<exists>y. x = y"
apply (rule allI)
apply (rule exI)
apply (rule refl)
done

lemma "\<exists>y. \<forall>x. x = y"
apply (rule exI)
apply (rule allI)
apply (rule refl)?
oops

text \<open>Parallel lifting example.\<close>
lemma "\<exists>u. \<forall>x. \<exists>v. \<forall>y. \<exists>w. P(u,x,v,y,w)"
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
oops

lemma
  assumes "(\<exists>z. F(z)) \<and> B"
  shows "\<exists>z. F(z) \<and> B"
apply (rule conjE)
apply (rule assms)
apply (rule exE)
apply assumption
apply (rule exI)
apply (rule conjI)
apply assumption
apply assumption
done

text \<open>A bigger demonstration of quantifiers -- not in the paper.\<close>
lemma "(\<exists>y. \<forall>x. Q(x,y)) \<longrightarrow> (\<forall>x. \<exists>y. Q(x,y))"
apply (rule impI)
apply (rule allI)
apply (rule exE, assumption)
apply (rule exI)
apply (rule allE, assumption)
apply assumption
done

end
