
simpset_ref() := LCF_ss;

Addsimps [F_strict,K];

goal thy "ALL x. F(H(x::'a,y::'b)) = H(x,F(y))";
by (stac H 1);
by (induct_tac "K::('a=>'b=>'b)=>('a=>'b=>'b)" 1);
by (Simp_tac 1);
by (asm_simp_tac (simpset() setloop (split_tac [COND_cases_iff])) 1);
qed "example";
