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

Goal "Numeral1^y = (Numeral1::int)";
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

