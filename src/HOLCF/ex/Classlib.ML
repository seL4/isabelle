open Classlib;

qed_goal "strict_qless" Classlib.thy "(UU .< x) = UU & (x .< UU) = UU"
 (fn prems =>
	[
	(simp_tac (HOLCF_ss addsimps [strict_qpo,qless_def,strict_per]) 1)
	]);

qed_goal "total_qless" Classlib.thy "[|x ~= UU; y ~= UU|] ==> (x .< y) ~= UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (HOLCF_ss addsimps [qless_def]) 1),
	(res_inst_tac [("p","x .= y")] trE 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_qpo,total_qpo,strict_per,total_per]) 1),
	(res_inst_tac [("P","x .= y = UU")] notE 1),
	(etac total_per 1),
	(atac 1),
	(atac 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_qpo,total_qpo,strict_per,total_per]) 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_qpo,total_qpo,strict_per,total_per]) 1)
	]);

qed_goal "irrefl_qless" Classlib.thy "[|x ~= UU|] ==> (x .< x)=FF"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(asm_simp_tac (HOLCF_ss addsimps [total_per,qless_def,refl_per]) 1)
	]);

qed_goal "asym_qless" Classlib.thy "~((x .< y)=TT & (y .< x)=TT)"
 (fn prems =>
	[
	(case_tac "x ~= UU & y ~= UU" 1),
	(etac conjE 1),
	(asm_simp_tac (HOLCF_ss addsimps [qless_def]) 1),
	(res_inst_tac [("p","x .= y")] trE 1),
	(asm_simp_tac HOLCF_ss 1),
	(asm_simp_tac HOLCF_ss 1),
	(asm_simp_tac HOLCF_ss 1),
	(rtac (sym_per RS subst) 1),
	(asm_simp_tac HOLCF_ss  1),
	(rtac (de_Morgan_conj RS iffD1) 1),
	(res_inst_tac [("Pa","(x .= y)=TT")] classical2 1),
	(asm_simp_tac (HOLCF_ss addsimps []) 1),
	(etac conjE 1),
	(rtac antisym_qpo 1),
	(atac 1),
	(atac 1),
	(subgoal_tac "x=UU Á y=UU" 1),
	(etac disjE 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_qless]) 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_qless]) 1),
	(fast_tac HOL_cs 1)
	]);


qed_goal "qless_iff" Classlib.thy "((x .< y)=TT) = ((x.=y)=FF & (x .<= y)=TT)"
 (fn prems =>
	[
	(rtac iffI 1),
	(asm_full_simp_tac (HOLCF_ss addsimps [qless_def]) 1),
	(res_inst_tac [("p","x .= y")] trE 1),
	(res_inst_tac [("P","TT=UU")] notE 1),
	(simp_tac (HOLCF_ss addsimps []) 1),
	(rtac trans 1),
	(etac sym 1),
	(asm_simp_tac (HOLCF_ss addsimps []) 1),
	(res_inst_tac [("P","TT=FF")] notE 1),
	(simp_tac (HOLCF_ss addsimps []) 1),
	(rtac trans 1),
	(etac sym 1),
	(asm_full_simp_tac (HOLCF_ss addsimps []) 1),
	(rtac conjI 1),
	(atac 1),
	(rtac trans 1),
	(atac 2),
	(asm_full_simp_tac (HOLCF_ss addsimps []) 1),
	(asm_full_simp_tac (HOLCF_ss addsimps [qless_def]) 1)
	]);

qed_goal "trans_qless" Classlib.thy "[|(x .< y)=TT; (y .< z)=TT |] ==> (x .< z)=TT"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (qless_iff RS iffD2) 1),
	(rtac conjI 1),
	(dtac (qless_iff RS iffD1) 1),
	(dtac (qless_iff RS iffD1) 1),
	(REPEAT (etac conjE 1)),
	(case_tac "x~=UU & z~=UU" 1),
	(REPEAT (etac conjE 1)),
	(res_inst_tac [("p","x .= z")] trE 1),
	(res_inst_tac [("P","x .= z = UU")] notE 1),
	(rtac total_per 1),
	(atac 1),
	(atac 1),
	(atac 1),
	(res_inst_tac [("P","TT = FF")] notE 1),
	(simp_tac (HOLCF_ss addsimps []) 1),
	(subgoal_tac "(y.=z)=TT" 1),
	(rtac trans 1),
	(etac sym 1),
	(atac 1),
	(rtac antisym_qpo 1),
	(atac 1),
	(rtac trans_qpo 1),
	(atac 2),
	(etac (antisym_qpo_rev RS conjunct2) 1),
	(atac 1),
	(dtac (de_Morgan_conj RS iffD1) 1),
	(etac disjE 1),
	(dtac notnotD 1),
	(res_inst_tac [("P","FF=UU")] notE 1),
	(simp_tac (HOLCF_ss addsimps []) 1),
	(rtac trans 1),
	(etac sym 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_per]) 1),
	(dtac notnotD 1),
	(res_inst_tac [("P","FF=UU")] notE 1),
	(simp_tac (HOLCF_ss addsimps []) 1),
	(rtac trans 1),
	(etac sym 1),
	(asm_simp_tac (HOLCF_ss addsimps [strict_per]) 1),
	(dtac (qless_iff RS iffD1) 1),
	(dtac (qless_iff RS iffD1) 1),
	(REPEAT (etac conjE 1)),
	(rtac trans_qpo 1),
	(atac 1),
	(atac 1)
	]);

(*

proof for transitivity depends on property antisym_qpo_rev
the proof is a bit lengthy

val prems = goal Classlib.thy "[|(x .< y)=TT; (y .< z)=TT |] ==> (x .< z)=TT";
by (cut_facts_tac prems 1);
by (rtac (qless_iff RS iffD2) 1);
by (rtac conjI 1);

by (dtac (qless_iff RS iffD1) 1);
by (dtac (qless_iff RS iffD1) 1);
by (REPEAT (etac conjE 1));
by (case_tac "x~=UU & z~=UU" 1);
by (REPEAT (etac conjE 1));
by (res_inst_tac [("p","x .= z")] trE 1);
by (res_inst_tac [("P","x .= z = UU")] notE 1);

by (rtac total_per 1);
by (atac 1);
by (atac 1);
by (atac 1);

by (res_inst_tac [("P","TT = FF")] notE 1);
by (simp_tac (HOLCF_ss addsimps []) 1);
by (subgoal_tac "(y.=z)=TT" 1);
by (rtac trans 1);
by (etac sym 1);
back();
back();
back();
by (atac 1);
by (rtac antisym_qpo 1);
by (atac 1);
by (rtac trans_qpo 1);
by (atac 2);
by (etac (antisym_qpo_rev RS conjunct2) 1);
by (atac 1);

by (dtac (de_Morgan_conj RS iffD1) 1);
by (etac disjE 1);
by (dtac notnotD 1);
by (res_inst_tac [("P","FF=UU")] notE 1);
by (simp_tac (HOLCF_ss addsimps []) 1);
by (rtac trans 1);
by (etac sym 1);
by (asm_simp_tac (HOLCF_ss addsimps [strict_per]) 1);

by (dtac notnotD 1);
by (res_inst_tac [("P","FF=UU")] notE 1);
by (simp_tac (HOLCF_ss addsimps []) 1);
by (rtac trans 1);
by (etac sym 1);
back();
by (asm_simp_tac (HOLCF_ss addsimps [strict_per]) 1);

by (dtac (qless_iff RS iffD1) 1);
by (dtac (qless_iff RS iffD1) 1);
by (REPEAT (etac conjE 1));
by (rtac trans_qpo 1);
by (atac 1);
by (atac 1);
val trans_qless = result();
*)
