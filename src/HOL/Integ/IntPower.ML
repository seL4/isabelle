(*  Title:	IntPower.thy
    ID:         $Id$
    Author:	Thomas M. Rasmussen
    Copyright	2000  University of Cambridge

Integer powers 
*)


Goal "((x::int) mod m)^y mod m = x^y mod m";
by (induct_tac "y" 1);
by Auto_tac;
by (rtac (zmod_zmult1_eq RS trans) 1);
by (Asm_simp_tac 1);
by (rtac (zmod_zmult_distrib RS sym) 1);
qed "zpower_zmod";

Goal "1^y = (1::int)";
by (induct_tac "y" 1);
by Auto_tac;
qed "zpower_1";
Addsimps [zpower_1];

Goal "(x*z)^y = ((x^y)*(z^y)::int)";
by (induct_tac "y" 1);
by Auto_tac;
qed "zpower_zmult_distrib";

Goal "x^(y+z) = ((x^y)*(x^z)::int)";
by (induct_tac "y" 1);
by Auto_tac;
qed "zpower_zadd_distrib";

Goal "(x^y)^z = (x^(y*z)::int)";
by (induct_tac "y" 1);
by Auto_tac;
by (stac zpower_zmult_distrib 1);
by (stac zpower_zadd_distrib 1);
by (Asm_simp_tac 1);
qed "zpower_zpower";


(*** Logical equivalences for inequalities ***)

Goal "(x^n = 0) = (x = (0::int) & 0<n)";
by (induct_tac "n" 1);
by Auto_tac; 
qed "zpower_eq_0_iff";
Addsimps [zpower_eq_0_iff];

Goal "(0 < (abs x)^n) = (x ~= (0::int) | n=0)";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [int_0_less_mult_iff]));  
qed "zero_less_zpower_abs_iff";
Addsimps [zero_less_zpower_abs_iff];

Goal "(0::int) <= (abs x)^n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [int_0_le_mult_iff]));  
qed "zero_le_zpower_abs";
Addsimps [zero_le_zpower_abs];
