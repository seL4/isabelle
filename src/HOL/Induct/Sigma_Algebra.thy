(*  Title:      HOL/Induct/Sigma_Algebra.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Sigma algebras\<close>

theory Sigma_Algebra
imports Main
begin

text \<open>
  This is just a tiny example demonstrating the use of inductive
  definitions in classical mathematics.  We define the least \<open>\<sigma>\<close>-algebra over a given set of sets.
\<close>

inductive_set \<sigma>_algebra :: "'a set set \<Rightarrow> 'a set set" for A :: "'a set set"
where
  basic: "a \<in> \<sigma>_algebra A" if "a \<in> A" for a
| UNIV: "UNIV \<in> \<sigma>_algebra A"
| complement: "- a \<in> \<sigma>_algebra A" if "a \<in> \<sigma>_algebra A" for a
| Union: "(\<Union>i. a i) \<in> \<sigma>_algebra A" if "\<And>i::nat. a i \<in> \<sigma>_algebra A" for a

text \<open>
  The following basic facts are consequences of the closure properties
  of any \<open>\<sigma>\<close>-algebra, merely using the introduction rules, but
  no induction nor cases.
\<close>

theorem sigma_algebra_empty: "{} \<in> \<sigma>_algebra A"
proof -
  have "UNIV \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.UNIV)
  then have "-UNIV \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.complement)
  also have "-UNIV = {}" by simp
  finally show ?thesis .
qed

theorem sigma_algebra_Inter:
  "(\<And>i::nat. a i \<in> \<sigma>_algebra A) \<Longrightarrow> (\<Inter>i. a i) \<in> \<sigma>_algebra A"
proof -
  assume "\<And>i::nat. a i \<in> \<sigma>_algebra A"
  then have "\<And>i::nat. -(a i) \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.complement)
  then have "(\<Union>i. -(a i)) \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.Union)
  then have "-(\<Union>i. -(a i)) \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.complement)
  also have "-(\<Union>i. -(a i)) = (\<Inter>i. a i)" by simp
  finally show ?thesis .
qed

end
