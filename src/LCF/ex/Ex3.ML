
simpset_ref() := LCF_ss;

Addsimps [p_strict,p_s];

goal thy "p(FIX(s),y) = FIX(s)";
by (induct_tac "s" 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "example";

