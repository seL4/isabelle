(*  Title:      HOL/Induct/Sigma_Algebra.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Sigma algebras *}

theory Sigma_Algebra = Main:

text {*
  This is just a tiny example demonstrating the use of inductive
  definitions in classical mathematics.  We define the least @{text
  \<sigma>}-algebra over a given set of sets.
*}

consts
  sigma_algebra :: "'a set set => 'a set set"    ("\<sigma>'_algebra")

inductive "\<sigma>_algebra A"
  intros
    basic: "a \<in> A ==> a \<in> \<sigma>_algebra A"
    UNIV: "UNIV \<in> \<sigma>_algebra A"
    complement: "a \<in> \<sigma>_algebra A ==> -a \<in> \<sigma>_algebra A"
    Union: "(!!i::nat. a i \<in> \<sigma>_algebra A) ==> (\<Union>i. a i) \<in> \<sigma>_algebra A"

text {*
  The following basic facts are consequences of the closure properties
  of any @{text \<sigma>}-algebra, merely using the introduction rules, but
  no induction nor cases.
*}

theorem sigma_algebra_empty: "{} \<in> \<sigma>_algebra A"
proof -
  have "UNIV \<in> \<sigma>_algebra A" by (rule sigma_algebra.UNIV)
  hence "-UNIV \<in> \<sigma>_algebra A" by (rule sigma_algebra.complement)
  also have "-UNIV = {}" by simp
  finally show ?thesis .
qed

theorem sigma_algebra_Inter:
  "(!!i::nat. a i \<in> \<sigma>_algebra A) ==> (\<Inter>i. a i) \<in> \<sigma>_algebra A"
proof -
  assume "!!i::nat. a i \<in> \<sigma>_algebra A"
  hence "!!i::nat. -(a i) \<in> \<sigma>_algebra A" by (rule sigma_algebra.complement)
  hence "(\<Union>i. -(a i)) \<in> \<sigma>_algebra A" by (rule sigma_algebra.Union)
  hence "-(\<Union>i. -(a i)) \<in> \<sigma>_algebra A" by (rule sigma_algebra.complement)
  also have "-(\<Union>i. -(a i)) = (\<Inter>i. a i)" by simp
  finally show ?thesis .
qed

end
