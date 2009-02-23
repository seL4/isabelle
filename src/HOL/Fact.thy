(*  Title       : Fact.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Factorial Function*}

theory Fact
imports Main
begin

consts fact :: "nat => nat"
primrec
  fact_0:     "fact 0 = 1"
  fact_Suc:   "fact (Suc n) = (Suc n) * fact n"


lemma fact_gt_zero [simp]: "0 < fact n"
by (induct n) auto

lemma fact_not_eq_zero [simp]: "fact n \<noteq> 0"
by simp

lemma of_nat_fact_not_zero [simp]: "of_nat (fact n) \<noteq> (0::'a::semiring_char_0)"
by auto

class ordered_semiring_1 = ordered_semiring + semiring_1
class ordered_semiring_1_strict = ordered_semiring_strict + semiring_1

lemma of_nat_fact_gt_zero [simp]: "(0::'a::{ordered_semidom}) < of_nat(fact n)" by auto

lemma of_nat_fact_ge_zero [simp]: "(0::'a::ordered_semidom) \<le> of_nat(fact n)"
by simp

lemma fact_ge_one [simp]: "1 \<le> fact n"
by (induct n) auto

lemma fact_mono: "m \<le> n ==> fact m \<le> fact n"
apply (drule le_imp_less_or_eq)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k, auto)
done

text{*Note that @{term "fact 0 = fact 1"}*}
lemma fact_less_mono: "[| 0 < m; m < n |] ==> fact m < fact n"
apply (drule_tac m = m in less_imp_Suc_add, auto)
apply (induct_tac k, auto)
done

lemma inv_of_nat_fact_gt_zero [simp]: "(0::'a::ordered_field) < inverse (of_nat (fact n))"
by (auto simp add: positive_imp_inverse_positive)

lemma inv_of_nat_fact_ge_zero [simp]: "(0::'a::ordered_field) \<le> inverse (of_nat (fact n))"
by (auto intro: order_less_imp_le)

lemma fact_diff_Suc [rule_format]:
  "n < Suc m ==> fact (Suc m - n) = (Suc m - n) * fact (m - n)"
apply (induct n arbitrary: m)
apply auto
apply (drule_tac x = "m - 1" in meta_spec, auto)
done

lemma fact_num0: "fact 0 = 1"
by auto

lemma fact_num_eq_if: "fact m = (if m=0 then 1 else m * fact (m - 1))"
by (cases m) auto

lemma fact_add_num_eq_if:
  "fact (m + n) = (if m + n = 0 then 1 else (m + n) * fact (m + n - 1))"
by (cases "m + n") auto

lemma fact_add_num_eq_if2:
  "fact (m + n) = (if m = 0 then fact n else (m + n) * fact ((m - 1) + n))"
by (cases m) auto

end
