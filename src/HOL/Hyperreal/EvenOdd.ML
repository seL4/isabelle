(*  Title       : Even.ML
    Author      : Jacques D. Fleuriot  
    Copyright   : 1999  University of Edinburgh
    Description : Even numbers defined
*)

Goal "even(Suc(Suc n)) = (even(n))";
by (Auto_tac);
qed "even_Suc_Suc";
Addsimps [even_Suc_Suc];

Goal "(even(n)) = (~odd(n))";
by (induct_tac "n" 1);
by (Auto_tac);
qed "even_not_odd";

Goal "(odd(n)) = (~even(n))";
by (simp_tac (simpset() addsimps [even_not_odd]) 1);
qed "odd_not_even";

Goal "even(2*n)";
by (induct_tac "n" 1);
by (Auto_tac);
qed "even_mult_two";
Addsimps [even_mult_two];

Goal "even(n*2)";
by (induct_tac "n" 1);
by (Auto_tac);
qed "even_mult_two'";
Addsimps [even_mult_two'];

Goal "even(n + n)";
by (induct_tac "n" 1);
by (Auto_tac);
qed "even_sum_self";
Addsimps [even_sum_self];

Goal "~odd(2*n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "not_odd_self_mult2";
Addsimps [not_odd_self_mult2];

Goal "~odd(n + n)";
by (induct_tac "n" 1);
by Auto_tac;
qed "not_odd_sum_self";
Addsimps [not_odd_sum_self];

Goal "~even(Suc(n + n))";
by (induct_tac "n" 1);
by Auto_tac;
qed "not_even_Suc_sum_self";
Addsimps [not_even_Suc_sum_self];

Goal "odd(Suc(2*n))";
by (induct_tac "n" 1);
by (Auto_tac);
qed "odd_mult_two_add_one";
Addsimps [odd_mult_two_add_one];

Goal "odd(Suc(n + n))";
by (induct_tac "n" 1);
by (Auto_tac);
qed "odd_sum_Suc_self";
Addsimps [odd_sum_Suc_self];

Goal "even(Suc n) = odd(n)";
by (induct_tac "n" 1);
by (Auto_tac);
qed "even_Suc_odd_iff";

Goal "odd(Suc n) = even(n)";
by (induct_tac "n" 1);
by (Auto_tac);
qed "odd_Suc_even_iff";

Goal "even n | odd n";
by (simp_tac (simpset() addsimps [even_not_odd]) 1);
qed "even_odd_disj";

(* could be proved automatically before: spoiled by numeral arith! *)
Goal "EX m. (n = 2*m | n = Suc(2*m))";
by (induct_tac "n" 1 THEN Auto_tac);
by (res_inst_tac [("x","Suc m")] exI 1 THEN Auto_tac);
qed "nat_mult_two_Suc_disj";

Goal "even(n) = (EX m. n = 2*m)";
by (cut_inst_tac [("n","n")] nat_mult_two_Suc_disj 1);
by (Auto_tac);
qed "even_mult_two_ex";

Goal "odd(n) = (EX m. n = Suc (2*m))";
by (cut_inst_tac [("n","n")] nat_mult_two_Suc_disj 1);
by (Auto_tac);
qed "odd_Suc_mult_two_ex";

Goal "even(n) ==> even(m*n)";
by (auto_tac (claset(),
              simpset() addsimps [add_mult_distrib2, even_mult_two_ex]));
qed "even_mult_even";
Addsimps [even_mult_even];

Goal "(m + m) div 2 = (m::nat)";
by (arith_tac 1);
qed "div_add_self_two_is_m";
Addsimps [div_add_self_two_is_m];

Goal "Suc(Suc(m*2)) div 2 = Suc m";
by (arith_tac 1);
qed "div_mult_self_Suc_Suc";
Addsimps [div_mult_self_Suc_Suc];

Goal "Suc(Suc(2*m)) div 2 = Suc m";
by (arith_tac 1);
qed "div_mult_self_Suc_Suc2";
Addsimps [div_mult_self_Suc_Suc2];

Goal "Suc(Suc(m + m)) div 2 = Suc m";
by (arith_tac 1);
qed "div_add_self_Suc_Suc";
Addsimps [div_add_self_Suc_Suc];

Goal "~ even n ==> (Suc n) div 2 = Suc((n - 1) div 2)";
by (auto_tac (claset(),simpset() addsimps [odd_not_even RS sym,
    odd_Suc_mult_two_ex]));
qed "not_even_imp_Suc_Suc_diff_one_eq";
Addsimps [not_even_imp_Suc_Suc_diff_one_eq];

Goal "even(m + n) = (even m = even n)";
by (induct_tac "m" 1);
by Auto_tac;
qed "even_add";
AddIffs [even_add];

Goal "even(m * n) = (even m | even n)";
by (induct_tac "m" 1);
by Auto_tac;
qed "even_mult";

Goal "even (m ^ n) = (even m & n ~= 0)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [even_mult]));
qed "even_pow";
AddIffs [even_pow];

Goal "odd(m + n) = (odd m ~= odd n)";
by (induct_tac "m" 1);
by Auto_tac;
qed "odd_add";
AddIffs [odd_add];

Goal "odd(m * n) = (odd m & odd n)";
by (induct_tac "m" 1);
by Auto_tac;
qed "odd_mult";
AddIffs [odd_mult];

Goal "odd (m ^ n) = (odd m | n = 0)";
by (induct_tac "n" 1);
by Auto_tac;
qed "odd_pow";

Goal "0 < n --> ~even (n + n - 1)";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "not_even_2n_minus_1";
Addsimps [not_even_2n_minus_1];

Goal "Suc (2 * m) mod 2 = 1";
by (induct_tac "m" 1);
by (auto_tac (claset(),simpset() addsimps [mod_Suc]));
qed "mod_two_Suc_2m";
Addsimps [mod_two_Suc_2m];

Goal "(Suc (Suc (2 * m)) div 2) = Suc m";
by (arith_tac 1);
qed "div_two_Suc_Suc_2m";
Addsimps [div_two_Suc_Suc_2m];

Goal "even n ==> 2 * ((n + 1) div 2) = n";
by (auto_tac (claset(),simpset() addsimps [mult_div_cancel,
    even_mult_two_ex]));
qed "lemma_even_div";
Addsimps [lemma_even_div];

Goal "~even n ==> 2 * ((n + 1) div 2) = Suc n";
by (auto_tac (claset(),simpset() addsimps [even_not_odd,
    odd_Suc_mult_two_ex]));
qed "lemma_not_even_div";
Addsimps [lemma_not_even_div];

Goal "Suc n div 2 <= Suc (Suc n) div 2";
by (arith_tac 1);
qed "Suc_n_le_Suc_Suc_n_div_2";
Addsimps [Suc_n_le_Suc_Suc_n_div_2];

Goal "(0::nat) < n --> 0 < (n + 1) div 2";
by (arith_tac 1);
qed_spec_mp "Suc_n_div_2_gt_zero";
Addsimps [Suc_n_div_2_gt_zero];

Goal "0 < n & even n --> 1 < n";
by (induct_tac "n" 1);
by Auto_tac;
qed_spec_mp "even_gt_zero_gt_one_aux";
bind_thm ("even_gt_zero_gt_one",conjI RS even_gt_zero_gt_one_aux);

(* more general *)
Goal "n div 2 <= (Suc n) div 2";
by (arith_tac 1);
qed "le_Suc_n_div_2";
Addsimps [le_Suc_n_div_2];

Goal "(1::nat) < n --> 0 < n div 2";
by (arith_tac 1);
qed_spec_mp "div_2_gt_zero";
Addsimps [div_2_gt_zero];

Goal "even n ==> (n + 1) div 2 = n div 2";
by (rtac (CLAIM "2 * x = 2 * y ==> x = (y::nat)") 1);
by (stac lemma_even_div 1);
by (auto_tac (claset(),simpset() addsimps [even_mult_two_ex]));
qed "lemma_even_div2";
Addsimps [lemma_even_div2];

Goal "~even n ==> (n + 1) div 2 = Suc (n div 2)";
by (rtac (CLAIM "2 * x = 2 * y ==> x = (y::nat)") 1);
by (stac lemma_not_even_div 1);
by (auto_tac (claset(),simpset() addsimps [even_not_odd,
    odd_Suc_mult_two_ex])); 
by (cut_inst_tac [("m","Suc(2*m)"),("n","2")] mod_div_equality 1); 
by Auto_tac; 
qed "lemma_not_even_div2";
Addsimps [lemma_not_even_div2];

Goal "(Suc n) div 2 = 0 ==> even n";
by (rtac ccontr 1);
by (dtac lemma_not_even_div2 1 THEN Auto_tac);
qed "Suc_n_div_two_zero_even";

Goal "0 < n ==> even n = (~ even(n - 1))";
by (case_tac "n" 1);
by Auto_tac;
qed "even_num_iff";

Goal "0 < n ==> odd n = (~ odd(n - 1))";
by (case_tac "n" 1);
by Auto_tac;
qed "odd_num_iff";

(* Some mod and div stuff *)

Goal "n ~= (0::nat) ==> (m = m div n * n + m mod n) & m mod n < n";
by (auto_tac (claset() addIs [mod_less_divisor],simpset()));
qed "mod_div_eq_less";

Goal "(k*n + m) mod n = m mod (n::nat)";
by (simp_tac (simpset() addsimps mult_ac @ add_ac) 1);
qed "mod_mult_self3";
Addsimps [mod_mult_self3];

Goal "Suc (k*n + m) mod n = Suc m mod n";
by (rtac (CLAIM "Suc (m + n) = (m + Suc n)" RS ssubst) 1);
by (rtac mod_mult_self3 1);
qed "mod_mult_self4";
Addsimps [mod_mult_self4];

Goal "Suc m mod n = Suc (m mod n) mod n";
by (cut_inst_tac [("d'","Suc (m mod n) mod n")] (CLAIM "EX d. d' = d") 1);
by (etac exE 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("t","m"),("n1","n")] (mod_div_equality RS subst) 1);
by (auto_tac (claset(),simpset() delsimprocs [cancel_div_mod_proc]));
qed "mod_Suc_eq_Suc_mod";

Goal "even n = (even (n mod 4))";
by (cut_inst_tac [("d'","(even (n mod 4))")] (CLAIM "EX d. d' = d") 1);
by (etac exE 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("t","n"),("n1","4")] (mod_div_equality RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [even_mult,even_num_iff] delsimprocs [cancel_div_mod_proc]));
qed "even_even_mod_4_iff";

Goal "odd n = (odd (n mod 4))";
by (auto_tac (claset(),simpset() addsimps [odd_not_even,
    even_even_mod_4_iff RS sym]));
qed "odd_odd_mod_4_iff";

Goal "odd n ==> ((-1) ^ n) = (-1::real)";
by (auto_tac (claset(),simpset() addsimps [odd_Suc_mult_two_ex]));
qed "odd_realpow_minus_one";
Addsimps [odd_realpow_minus_one];

Goal "even(4*n)";
by (auto_tac (claset(),simpset() addsimps [even_mult_two_ex]));
qed "even_4n";
Addsimps [even_4n];

Goal "n mod 4 = 0 ==> even(n div 2)";
by Auto_tac;
qed "lemma_even_div_2";

Goal "n mod 4 = 0 ==> even(n)";
by Auto_tac;
qed "lemma_mod_4_even_n";

Goal "n mod 4 = 1 ==> odd(n)";
by (res_inst_tac [("t","n"),("n1","4")] (mod_div_equality RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [odd_num_iff] delsimprocs [cancel_div_mod_proc]));
qed "lemma_mod_4_odd_n";

Goal "n mod 4 = 2 ==> even(n)";
by (res_inst_tac [("t","n"),("n1","4")] (mod_div_equality RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [even_num_iff] delsimprocs [cancel_div_mod_proc]));
qed "lemma_mod_4_even_n2";

Goal "n mod 4 = 3 ==> odd(n)";
by (res_inst_tac [("t","n"),("n1","4")] (mod_div_equality RS subst) 1);
by (auto_tac (claset(),simpset() addsimps [odd_num_iff] delsimprocs [cancel_div_mod_proc]));
qed "lemma_mod_4_odd_n2";

Goal "even n ==> ((-1) ^ n) = (1::real)";
by (auto_tac (claset(),simpset() addsimps [even_mult_two_ex]));
qed "even_realpow_minus_one";
Addsimps [even_realpow_minus_one];

Goal "((4 * n) + 2) div 2 = (2::nat) * n + 1";
by (arith_tac 1);
qed "lemma_4n_add_2_div_2_eq";
Addsimps [lemma_4n_add_2_div_2_eq];

Goal "(Suc(Suc(4 * n))) div 2 = (2::nat) * n + 1";
by (arith_tac 1);
qed "lemma_Suc_Suc_4n_div_2_eq";
Addsimps [lemma_Suc_Suc_4n_div_2_eq];

Goal "(Suc(Suc(n * 4))) div 2 = (2::nat) * n + 1";
by (arith_tac 1);
qed "lemma_Suc_Suc_4n_div_2_eq2";
Addsimps [lemma_Suc_Suc_4n_div_2_eq2];

Goal "n mod 4 = 3 ==> odd((n - 1) div 2)";
by (res_inst_tac [("t","n"),("n1","4")] (mod_div_equality RS subst) 1);
by (asm_full_simp_tac (simpset() addsimps [odd_num_iff] delsimprocs [cancel_div_mod_proc]) 1);
val lemma_odd_mod_4_div_2 = result();

Goal "(4 * n) div 2 = (2::nat) * n";
by (arith_tac 1);
qed "lemma_4n_div_2_eq";
Addsimps [lemma_4n_div_2_eq];

Goal "(n  * 4) div 2 = (2::nat) * n";
by (arith_tac 1);
qed "lemma_4n_div_2_eq2";
Addsimps [lemma_4n_div_2_eq2];

Goal "n mod 4 = 1 ==> even ((n - 1) div 2)";
by (res_inst_tac [("t","n"),("n1","4")] (mod_div_equality RS subst) 1);
by (dtac ssubst 1 THEN assume_tac 2);
by (rtac ((CLAIM "(n::nat) + 1 - 1 = n") RS ssubst) 1);
by Auto_tac;
val lemma_even_mod_4_div_2 = result();


