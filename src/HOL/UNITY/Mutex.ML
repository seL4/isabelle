(*  Title:      HOL/UNITY/Mutex
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

val cmd_defs = [Mprg_def, 
		cmd0U_def, cmd1U_def, cmd2U_def, cmd3U_def, cmd4U_def, 
		cmd0V_def, cmd1V_def, cmd2V_def, cmd3V_def, cmd4V_def];

Goalw [Mprg_def] "id : Acts Mprg";
by (Simp_tac 1);
qed "id_in_Acts";
AddIffs [id_in_Acts];


(*Simplification for records*)
val select_defs = thms"state.select_defs"
and update_defs = thms"state.update_defs"
and dest_defs   = thms"state.dest_defs";

Addsimps update_defs;

Addsimps [invariantU_def, invariantV_def];


Goalw [Mprg_def] "Invariant Mprg invariantU";
by (rtac InvariantI 1);
by (constrains_tac cmd_defs 2);
by Auto_tac;
qed "invariantU";

Goalw [Mprg_def] "Invariant Mprg invariantV";
by (rtac InvariantI 1);
by (constrains_tac cmd_defs 2);
by Auto_tac;
qed "invariantV";

val invariantUV = Invariant_Int_rule [invariantU, invariantV];


(*The safety property: mutual exclusion*)
Goal "(reachable Mprg) Int {s. MM s = 3 & NN s = 3} = {}";
by (cut_facts_tac [invariantUV RS Invariant_includes_reachable] 1);
by Auto_tac;
qed "mutual_exclusion";


(*The bad invariant FAILS in cmd1V*)
Goalw [Mprg_def, bad_invariantU_def] "Invariant Mprg bad_invariantU";
by (rtac InvariantI 1);
by (Force_tac 1);
by (constrains_tac cmd_defs 1);
by (safe_tac (claset() addSEs [le_SucE]));
by (Asm_full_simp_tac 1);
(*Resulting state: n=1, p=false, m=4, u=false.  
  Execution of cmd1V (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
(*Check that subgoals remain: proof failed.*)
getgoal 1;  


(*** Progress for U ***)

Goalw [Unless_def] "Unless Mprg {s. MM s=2} {s. MM s=3}";
by (constrains_tac cmd_defs 1);
qed "U_F0";

Goal "LeadsTo Mprg {s. MM s=1} {s. PP s = VV s & MM s = 2}";
by (ensures_tac cmd_defs "cmd1U" 1);
qed "U_F1";

Goal "LeadsTo Mprg {s. ~ PP s & MM s = 2} {s. MM s = 3}";
by (cut_facts_tac [invariantU] 1);
by (rewtac Mprg_def);
by (ensures_tac cmd_defs "cmd2U" 1);
qed "U_F2";

Goal "LeadsTo Mprg {s. MM s = 3} {s. PP s}";
by (res_inst_tac [("B", "{s. MM s = 4}")] LeadsTo_Trans 1);
by (ensures_tac cmd_defs "cmd4U" 2);
by (ensures_tac cmd_defs "cmd3U" 1);
qed "U_F3";

Goal "LeadsTo Mprg {s. MM s = 2} {s. PP s}";
by (rtac ([LeadsTo_weaken_L, Int_lower2 RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val U_lemma2 = result();

Goal "LeadsTo Mprg {s. MM s = 1} {s. PP s}";
by (rtac ([U_F1 RS LeadsTo_weaken_R, U_lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val U_lemma1 = result();

Goal "LeadsTo Mprg {s. 1 <= MM s & MM s <= 3} {s. PP s}";
by (simp_tac (simpset() addsimps [le_Suc_eq, conj_disj_distribL] 
	                addcongs [rev_conj_cong]) 1);
by (simp_tac (simpset() addsimps [Collect_disj_eq, LeadsTo_Un_distrib,
				  U_lemma1, U_lemma2, U_F3] ) 1);
val U_lemma123 = result();

(*Misra's F4*)
Goal "LeadsTo Mprg {s. UU s} {s. PP s}";
by (rtac ([invariantU, U_lemma123] MRS Invariant_LeadsTo_weaken) 1);
by Auto_tac;
qed "u_Leadsto_p";


(*** Progress for V ***)


Goalw [Unless_def] "Unless Mprg {s. NN s=2} {s. NN s=3}";
by (constrains_tac cmd_defs 1);
qed "V_F0";

Goal "LeadsTo Mprg {s. NN s=1} {s. PP s = (~ UU s) & NN s = 2}";
by (ensures_tac cmd_defs "cmd1V" 1);
qed "V_F1";

Goal "LeadsTo Mprg {s. PP s & NN s = 2} {s. NN s = 3}";
by (cut_facts_tac [invariantV] 1);
by (ensures_tac cmd_defs "cmd2V" 1);
qed "V_F2";

Goal "LeadsTo Mprg {s. NN s = 3} {s. ~ PP s}";
by (res_inst_tac [("B", "{s. NN s = 4}")] LeadsTo_Trans 1);
by (ensures_tac cmd_defs "cmd4V" 2);
by (ensures_tac cmd_defs "cmd3V" 1);
qed "V_F3";

Goal "LeadsTo Mprg {s. NN s = 2} {s. ~ PP s}";
by (rtac ([LeadsTo_weaken_L, Int_lower2 RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([V_F2, V_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val V_lemma2 = result();

Goal "LeadsTo Mprg {s. NN s = 1} {s. ~ PP s}";
by (rtac ([V_F1 RS LeadsTo_weaken_R, V_lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val V_lemma1 = result();

Goal "LeadsTo Mprg {s. 1 <= NN s & NN s <= 3} {s. ~ PP s}";
by (simp_tac (simpset() addsimps [le_Suc_eq, conj_disj_distribL] 
	                addcongs [rev_conj_cong]) 1);
by (simp_tac (simpset() addsimps [Collect_disj_eq, LeadsTo_Un_distrib,
				  V_lemma1, V_lemma2, V_F3] ) 1);
val V_lemma123 = result();


(*Misra's F4*)
Goal "LeadsTo Mprg {s. VV s} {s. ~ PP s}";
by (rtac ([invariantV, V_lemma123] MRS Invariant_LeadsTo_weaken) 1);
by Auto_tac;
qed "v_Leadsto_not_p";


(** Absence of starvation **)

(*Misra's F6*)
Goal "LeadsTo Mprg {s. MM s = 1} {s. MM s = 3}";
by (rtac LeadsTo_Un_duplicate 1);
by (rtac LeadsTo_cancel2 1);
by (rtac U_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac LeadsTo_Un_duplicate 1);
by (rtac ([v_Leadsto_not_p, U_F0] MRS PSP_Unless RSN(2, LeadsTo_cancel2)) 1);
by (rtac (U_F1 RS LeadsTo_weaken_R) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "m1_Leadsto_3";


(*The same for V*)
Goal "LeadsTo Mprg {s. NN s = 1} {s. NN s = 3}";
by (rtac LeadsTo_Un_duplicate 1);
by (rtac LeadsTo_cancel2 1);
by (rtac V_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac LeadsTo_Un_duplicate 1);
by (rtac ([u_Leadsto_p, V_F0] MRS PSP_Unless  RSN(2, LeadsTo_cancel2)) 1);
by (rtac (V_F1 RS LeadsTo_weaken_R) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "n1_Leadsto_3";
