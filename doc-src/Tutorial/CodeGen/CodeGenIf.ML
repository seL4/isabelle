Addsimps exec.rules;
Addsimps [Let_def,drop_all];
Addsplits [split_instr_case];

Goal "!xs. wf xs --> wf(drop n xs)";
by(induct_tac "n" 1);
by(Simp_tac 1);
by(Clarify_tac 1);
by(exhaust_tac "xs" 1);
by(Asm_simp_tac 1);
by(Asm_full_simp_tac 1);
qed_spec_mp "wf_drop";
Addsimps [wf_drop];

Goal "wf xs --> wf ys --> wf(xs@ys)";
by(induct_tac "xs" 1);
by(Simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [trans_le_add1]) 1);
qed_spec_mp "wf_append";
Addsimps [wf_append];

Goal "!vs ys. wf xs --> exec(s,vs,xs@ys) = exec(s,exec(s,vs,xs),ys)"; 
by(res_inst_tac [("xs","xs")] length_induct 1);
by(exhaust_tac "xs" 1);
by(Asm_full_simp_tac 1);
by(asm_full_simp_tac (simpset() addsimps [less_imp_diff_is_0,diff_less_Suc,le_imp_less_Suc]) 1);
qed_spec_mp "exec_append";
Addsimps [exec_append];

Goal "wf(comp e)";
by(induct_tac "e" 1);
by(ALLGOALS Asm_simp_tac);
qed "wf_comp";
Addsimps [wf_comp];

Goal "!vs. exec(s, vs, comp e) = (value s e) # vs";
by(induct_tac "e" 1);
by(ALLGOALS Asm_simp_tac);
qed "exec_comp";
