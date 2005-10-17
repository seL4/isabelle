
(* $Id$ *)

Addsimps [p_strict,p_s];

Goal "p(FIX(s),y) = FIX(s)";
by (induct_tac "s" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "example";
