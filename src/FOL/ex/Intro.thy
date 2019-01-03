(*  Title:      FOL/ex/Intro.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Derives some inference rules, illustrating the use of definitions.
*)

section \<open>Examples for the manual ``Introduction to Isabelle''\<close>

theory Intro
imports FOL
begin

subsubsection \<open>Some simple backward proofs\<close>

lemma mythm: \<open>P \<or> P \<longrightarrow> P\<close>
apply (rule impI)
apply (rule disjE)
prefer 3 apply (assumption)
prefer 2 apply (assumption)
apply assumption
done

lemma \<open>(P \<and> Q) \<or> R \<longrightarrow> (P \<or> R)\<close>
apply (rule impI)
apply (erule disjE)
apply (drule conjunct1)
apply (rule disjI1)
apply (rule_tac [2] disjI2)
apply assumption+
done

text \<open>Correct version, delaying use of \<open>spec\<close> until last.\<close>
lemma \<open>(\<forall>x y. P(x,y)) \<longrightarrow> (\<forall>z w. P(w,z))\<close>
apply (rule impI)
apply (rule allI)
apply (rule allI)
apply (drule spec)
apply (drule spec)
apply assumption
done


subsubsection \<open>Demonstration of \<open>fast\<close>\<close>

lemma \<open>(\<exists>y. \<forall>x. J(y,x) \<longleftrightarrow> \<not> J(x,x)) \<longrightarrow> \<not> (\<forall>x. \<exists>y. \<forall>z. J(z,y) \<longleftrightarrow> \<not> J(z,x))\<close>
apply fast
done


lemma \<open>\<forall>x. P(x,f(x)) \<longleftrightarrow> (\<exists>y. (\<forall>z. P(z,y) \<longrightarrow> P(z,f(x))) \<and> P(x,y))\<close>
apply fast
done


subsubsection \<open>Derivation of conjunction elimination rule\<close>

lemma
  assumes major: \<open>P \<and> Q\<close>
    and minor: \<open>\<lbrakk>P; Q\<rbrakk> \<Longrightarrow> R\<close>
  shows \<open>R\<close>
apply (rule minor)
apply (rule major [THEN conjunct1])
apply (rule major [THEN conjunct2])
done


subsection \<open>Derived rules involving definitions\<close>

text \<open>Derivation of negation introduction\<close>

lemma
  assumes \<open>P \<Longrightarrow> False\<close>
  shows \<open>\<not> P\<close>
apply (unfold not_def)
apply (rule impI)
apply (rule assms)
apply assumption
done

lemma
  assumes major: \<open>\<not> P\<close>
    and minor: \<open>P\<close>
  shows \<open>R\<close>
apply (rule FalseE)
apply (rule mp)
apply (rule major [unfolded not_def])
apply (rule minor)
done

text \<open>Alternative proof of the result above\<close>
lemma
  assumes major: \<open>\<not> P\<close>
    and minor: \<open>P\<close>
  shows \<open>R\<close>
apply (rule minor [THEN major [unfolded not_def, THEN mp, THEN FalseE]])
done

end
