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
