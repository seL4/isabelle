(*  Title:      HOL/Integ/IntArith.ML
    ID:         $Id$
    Authors:    Larry Paulson and Tobias Nipkow
*)

Goal "abs(abs(x::int)) = abs(x)";
by(arith_tac 1);
qed "abs_abs";
Addsimps [abs_abs];

Goal "abs(-(x::int)) = abs(x)";
by(arith_tac 1);
qed "abs_minus";
Addsimps [abs_minus];

Goal "abs(x+y) <= abs(x) + abs(y::int)";
by(arith_tac 1);
qed "triangle_ineq";


(*** Some convenient biconditionals for products of signs ***)

Goal "[| (#0::int) < i; #0 < j |] ==> #0 < i*j";
by (dtac zmult_zless_mono1 1);
by Auto_tac; 
qed "zmult_pos";

Goal "[| i < (#0::int); j < #0 |] ==> #0 < i*j";
by (dtac zmult_zless_mono1_neg 1);
by Auto_tac; 
qed "zmult_neg";

Goal "[| (#0::int) < i; j < #0 |] ==> i*j < #0";
by (dtac zmult_zless_mono1_neg 1);
by Auto_tac; 
qed "zmult_pos_neg";

Goal "((#0::int) < x*y) = (#0 < x & #0 < y | x < #0 & y < #0)";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, linorder_not_less,
	                          zmult_pos, zmult_neg]));
by (ALLGOALS (rtac ccontr)); 
by (auto_tac (claset(), 
	      simpset() addsimps [order_le_less, linorder_not_less]));
by (ALLGOALS (etac rev_mp)); 
by (ALLGOALS (dtac zmult_pos_neg THEN' assume_tac));
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [zmult_commute]));  
qed "int_0_less_mult_iff";

Goal "((#0::int) <= x*y) = (#0 <= x & #0 <= y | x <= #0 & y <= #0)";
by (auto_tac (claset(), 
              simpset() addsimps [order_le_less, linorder_not_less,  
                                  int_0_less_mult_iff]));
qed "int_0_le_mult_iff";

Goal "(x*y < (#0::int)) = (#0 < x & y < #0 | x < #0 & #0 < y)";
by (auto_tac (claset(), 
              simpset() addsimps [int_0_le_mult_iff, 
                                  linorder_not_le RS sym]));
by (auto_tac (claset() addDs [order_less_not_sym],  
              simpset() addsimps [linorder_not_le]));
qed "zmult_less_0_iff";

Goal "(x*y <= (#0::int)) = (#0 <= x & y <= #0 | x <= #0 & #0 <= y)";
by (auto_tac (claset() addDs [order_less_not_sym], 
              simpset() addsimps [int_0_less_mult_iff, 
                                  linorder_not_less RS sym]));
qed "zmult_le_0_iff";


(*** Products and 1, by T. M. Rasmussen ***)

Goal "(m = m*(n::int)) = (n = #1 | m = #0)";
by Auto_tac;
by (subgoal_tac "m*#1 = m*n" 1);
by (dtac (zmult_cancel1 RS iffD1) 1); 
by Auto_tac;
qed "zmult_eq_self_iff";

Goal "[| #1 < m; #1 < n |] ==> #1 < m*(n::int)";
by (res_inst_tac [("z2.0","#1*n")] zless_trans 1);
by (rtac zmult_zless_mono1 2);
by (ALLGOALS Asm_simp_tac);
qed "zless_1_zmult";

Goal "[| #0 < n; n ~= #1 |] ==> #1 < (n::int)";
by (arith_tac 1);
val lemma = result();

Goal "#0 < (m::int) ==> (m * n = #1) = (m = #1 & n = #1)";
by Auto_tac;
by (case_tac "m=#1" 1);
by (case_tac "n=#1" 2);
by (case_tac "m=#1" 4);
by (case_tac "n=#1" 5);
by Auto_tac;
by distinct_subgoals_tac;
by (subgoal_tac "#1<m*n" 1);
by (Asm_full_simp_tac 1);
by (rtac zless_1_zmult 1);
by (ALLGOALS (rtac lemma));
by Auto_tac;  
by (subgoal_tac "#0<m*n" 1);
by (Asm_simp_tac 2);
by (dtac (int_0_less_mult_iff RS iffD1) 1);
by Auto_tac;  
qed "pos_zmult_eq_1_iff";

Goal "(m*n = (#1::int)) = ((m = #1 & n = #1) | (m = #-1 & n = #-1))";
by (case_tac "#0<m" 1);
by (asm_simp_tac (simpset() addsimps [pos_zmult_eq_1_iff]) 1);
by (case_tac "m=#0" 1);
by (Asm_simp_tac 1);
by (subgoal_tac "#0 < -m" 1);
by (arith_tac 2);
by (dres_inst_tac [("n","-n")] pos_zmult_eq_1_iff 1); 
by Auto_tac;  
qed "zmult_eq_1_iff";

