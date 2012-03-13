(*  Title:      HOL/Induct/Sigma_Algebra.thy
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Sigma algebras *}

theory Sigma_Algebra
imports Main
begin

text {*
  This is just a tiny example demonstrating the use of inductive
  definitions in classical mathematics.  We define the least @{text
  \<sigma>}-algebra over a given set of sets.
*}

inductive_set \<sigma>_algebra :: "'a set set => 'a set set" for A :: "'a set set"
where
  basic: "a \<in> A ==> a \<in> \<sigma>_algebra A"
| UNIV: "UNIV \<in> \<sigma>_algebra A"
| complement: "a \<in> \<sigma>_algebra A ==> -a \<in> \<sigma>_algebra A"
| Union: "(!!i::nat. a i \<in> \<sigma>_algebra A) ==> (\<Union>i. a i) \<in> \<sigma>_algebra A"

text {*
  The following basic facts are consequences of the closure properties
  of any @{text \<sigma>}-algebra, merely using the introduction rules, but
  no induction nor cases.
*}

theorem sigma_algebra_empty: "{} \<in> \<sigma>_algebra A"
proof -
  have "UNIV \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.UNIV)
  then have "-UNIV \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.complement)
  also have "-UNIV = {}" by simp
  finally show ?thesis .
qed

theorem sigma_algebra_Inter:
  "(!!i::nat. a i \<in> \<sigma>_algebra A) ==> (\<Inter>i. a i) \<in> \<sigma>_algebra A"
proof -
  assume "!!i::nat. a i \<in> \<sigma>_algebra A"
  then have "!!i::nat. -(a i) \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.complement)
  then have "(\<Union>i. -(a i)) \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.Union)
  then have "-(\<Union>i. -(a i)) \<in> \<sigma>_algebra A" by (rule \<sigma>_algebra.complement)
  also have "-(\<Union>i. -(a i)) = (\<Inter>i. a i)" by simp
  finally show ?thesis .
qed

end
