(*  Title       : Fact.ML
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Factorial function
*)

Goal "0 < fact n";
by (induct_tac "n" 1);
by (Auto_tac);
qed "fact_gt_zero";
Addsimps [fact_gt_zero];

Goal "fact n ~= 0";
by (Simp_tac 1);
qed "fact_not_eq_zero";
Addsimps [fact_not_eq_zero];

Goal "real (fact n) ~= 0";
by Auto_tac; 
qed "real_of_nat_fact_not_zero";
Addsimps [real_of_nat_fact_not_zero];

Goal "0 < real(fact n)";
by Auto_tac; 
qed "real_of_nat_fact_gt_zero";
Addsimps [real_of_nat_fact_gt_zero];

Goal "0 <= real(fact n)";
by (Simp_tac 1);
qed "real_of_nat_fact_ge_zero";
Addsimps [real_of_nat_fact_ge_zero];

Goal "1 <= fact n";
by (induct_tac "n" 1);
by (Auto_tac);
qed "fact_ge_one";
Addsimps [fact_ge_one];

Goal "m <= n ==> fact m <= fact n";
by (dtac le_imp_less_or_eq 1);
by (auto_tac (claset() addSDs [less_imp_Suc_add],simpset()));
by (induct_tac "k" 1);
by (Auto_tac);
qed "fact_mono";

Goal "[| 0 < m; m < n |] ==> fact m < fact n";
by (dres_inst_tac [("m","m")] less_imp_Suc_add 1);
by Auto_tac;
by (induct_tac "k" 1);
by (Auto_tac);
qed "fact_less_mono";

Goal "0 < inverse (real (fact n))";
by (auto_tac (claset(),simpset() addsimps [positive_imp_inverse_positive]));
qed "inv_real_of_nat_fact_gt_zero";
Addsimps [inv_real_of_nat_fact_gt_zero];

Goal "0 <= inverse (real (fact n))";
by (auto_tac (claset() addIs [order_less_imp_le],simpset()));
qed "inv_real_of_nat_fact_ge_zero";
Addsimps [inv_real_of_nat_fact_ge_zero];

Goal "ALL m. ma < Suc m --> fact (Suc m - ma) = (Suc m - ma) * fact (m - ma)";
by (induct_tac "ma" 1);
by Auto_tac;
by (dres_inst_tac [("x","m - 1")] spec 1);
by Auto_tac;
qed_spec_mp "fact_diff_Suc";

Goal "fact 0 = 1";
by Auto_tac;
qed "fact_num0";
Addsimps [fact_num0];

Goal "fact m = (if m=0 then 1 else m * fact (m - 1))";
by (case_tac "m" 1);
by Auto_tac;
qed "fact_num_eq_if";

Goal "fact (m + n) = (if (m + n = 0) then 1 else (m + n) * (fact (m + n - 1)))";
by (case_tac "m+n" 1);
by Auto_tac;
qed "fact_add_num_eq_if";

Goal "fact (m + n) = (if (m = 0) then fact n \
\     else (m + n) * (fact ((m - 1) + n)))";
by (case_tac "m" 1);
by Auto_tac;
qed "fact_add_num_eq_if2";

