(*  Title:      FOL/ex/Foundation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1991  University of Cambridge
*)

section "Intuitionistic FOL: Examples from The Foundation of a Generic Theorem Prover"

theory Foundation
imports IFOL
begin

lemma \<open>A \<and> B \<longrightarrow> (C \<longrightarrow> A \<and> C)\<close>
apply (rule impI)
apply (rule impI)
apply (rule conjI)
prefer 2 apply assumption
apply (rule conjunct1)
apply assumption
done

text \<open>A form of conj-elimination\<close>
lemma
  assumes \<open>A \<and> B\<close>
    and \<open>A \<Longrightarrow> B \<Longrightarrow> C\<close>
  shows \<open>C\<close>
apply (rule assms)
apply (rule conjunct1)
apply (rule assms)
apply (rule conjunct2)
apply (rule assms)
done

lemma
  assumes \<open>\<And>A. \<not> \<not> A \<Longrightarrow> A\<close>
  shows \<open>B \<or> \<not> B\<close>
apply (rule assms)
apply (rule notI)
apply (rule_tac P = \<open>\<not> B\<close> in notE)
apply (rule_tac [2] notI)
apply (rule_tac [2] P = \<open>B \<or> \<not> B\<close> in notE)
prefer 2 apply assumption
apply (rule_tac [2] disjI1)
prefer 2 apply assumption
apply (rule notI)
apply (rule_tac P = \<open>B \<or> \<not> B\<close> in notE)
apply assumption
apply (rule disjI2)
apply assumption
done

lemma
  assumes \<open>\<And>A. \<not> \<not> A \<Longrightarrow> A\<close>
  shows \<open>B \<or> \<not> B\<close>
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
  assumes \<open>A \<or> \<not> A\<close>
    and \<open>\<not> \<not> A\<close>
  shows \<open>A\<close>
apply (rule disjE)
apply (rule assms)
apply assumption
apply (rule FalseE)
apply (rule_tac P = \<open>\<not> A\<close> in notE)
apply (rule assms)
apply assumption
done


subsection "Examples with quantifiers"

lemma
  assumes \<open>\<forall>z. G(z)\<close>
  shows \<open>\<forall>z. G(z) \<or> H(z)\<close>
apply (rule allI)
apply (rule disjI1)
apply (rule assms [THEN spec])
done

lemma \<open>\<forall>x. \<exists>y. x = y\<close>
apply (rule allI)
apply (rule exI)
apply (rule refl)
done

lemma \<open>\<exists>y. \<forall>x. x = y\<close>
apply (rule exI)
apply (rule allI)
apply (rule refl)?
oops

text \<open>Parallel lifting example.\<close>
lemma \<open>\<exists>u. \<forall>x. \<exists>v. \<forall>y. \<exists>w. P(u,x,v,y,w)\<close>
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
apply (rule exI allI)
oops

lemma
  assumes \<open>(\<exists>z. F(z)) \<and> B\<close>
  shows \<open>\<exists>z. F(z) \<and> B\<close>
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
lemma \<open>(\<exists>y. \<forall>x. Q(x,y)) \<longrightarrow> (\<forall>x. \<exists>y. Q(x,y))\<close>
apply (rule impI)
apply (rule allI)
apply (rule exE, assumption)
apply (rule exI)
apply (rule allE, assumption)
apply assumption
done

end
