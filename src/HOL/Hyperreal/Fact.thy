(*  Title       : Fact.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Factorial Function*}

theory Fact
import Real
begin

consts fact :: "nat => nat"
primrec
   fact_0:     "fact 0 = 1"
   fact_Suc:   "fact (Suc n) = (Suc n) * fact n"


lemma fact_gt_zero [simp]: "0 < fact n"
by (induct "n", auto)

lemma fact_not_eq_zero [simp]: "fact n \<noteq> 0"
by simp

lemma real_of_nat_fact_not_zero [simp]: "real (fact n) \<noteq> 0"
by auto

lemma real_of_nat_fact_gt_zero [simp]: "0 < real(fact n)"
by auto

lemma real_of_nat_fact_ge_zero [simp]: "0 \<le> real(fact n)"
by simp

lemma fact_ge_one [simp]: "1 \<le> fact n"
by (induct "n", auto)

lemma fact_mono: "m \<le> n ==> fact m \<le> fact n"
apply (drule le_imp_less_or_eq)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac "k", auto)
done

text{*Note that @{term "fact 0 = fact 1"}*}
lemma fact_less_mono: "[| 0 < m; m < n |] ==> fact m < fact n"
apply (drule_tac m = m in less_imp_Suc_add, auto)
apply (induct_tac "k", auto)
done

lemma inv_real_of_nat_fact_gt_zero [simp]: "0 < inverse (real (fact n))"
by (auto simp add: positive_imp_inverse_positive)

lemma inv_real_of_nat_fact_ge_zero [simp]: "0 \<le> inverse (real (fact n))"
by (auto intro: order_less_imp_le)

lemma fact_diff_Suc [rule_format]:
     "\<forall>m. n < Suc m --> fact (Suc m - n) = (Suc m - n) * fact (m - n)"
apply (induct n, auto)
apply (drule_tac x = "m - 1" in spec, auto)
done

lemma fact_num0 [simp]: "fact 0 = 1"
by auto

lemma fact_num_eq_if: "fact m = (if m=0 then 1 else m * fact (m - 1))"
by (case_tac "m", auto)

lemma fact_add_num_eq_if:
     "fact (m+n) = (if (m+n = 0) then 1 else (m+n) * (fact (m + n - 1)))"
by (case_tac "m+n", auto)

lemma fact_add_num_eq_if2:
     "fact (m+n) = (if m=0 then fact n else (m+n) * (fact ((m - 1) + n)))"
by (case_tac "m", auto)


end
