(*  Title:      HOL/UNITY/Mutex
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

(*split_all_tac causes a big blow-up*)
claset_ref() := claset() delSWrapper "split_all_tac";

val cmd_defs = [mutex_def, 
		cmd0U_def, cmd1U_def, cmd2U_def, cmd3U_def, cmd4U_def, 
		cmd0V_def, cmd1V_def, cmd2V_def, cmd3V_def, cmd4V_def];

Goalw [mutex_def] "id : mutex";
by (Simp_tac 1);
qed "id_in_mutex";
AddIffs [id_in_mutex];


(*Simplification for records*)
val select_defs = thms"state.select_defs"
and update_defs = thms"state.update_defs"
and dest_defs   = thms"state.dest_defs";

Addsimps update_defs;


(** Constrains/Ensures tactics: NEED TO BE GENERALIZED OVER ALL PROGRAMS
     [They have free occurrences of mutex_def and cmd_defs] **)

(*proves "constrains" properties when the program is specified*)
val constrains_tac = 
   SELECT_GOAL
      (EVERY [rtac constrainsI 1,
	      rewtac mutex_def,
	      REPEAT_FIRST (eresolve_tac [insertE, emptyE]),
	      rewrite_goals_tac cmd_defs,
	      ALLGOALS (SELECT_GOAL Auto_tac)]);


(*proves "ensures" properties when the program is specified*)
fun ensures_tac sact = 
    SELECT_GOAL
      (EVERY [etac reachable_LeadsTo_Basis 1 
	          ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
		  REPEAT (ares_tac [leadsTo_imp_LeadsTo, leadsTo_Basis, 
				    ensuresI] 1),
	      res_inst_tac [("act", sact)] transient_mem 2,
	      simp_tac (simpset() addsimps (Domain_partial_func::cmd_defs)) 3,
	      simp_tac (simpset() addsimps [mutex_def]) 2,
	      constrains_tac 1,
	      rewrite_goals_tac cmd_defs,
	      ALLGOALS Clarify_tac,
	      Auto_tac]);


Goalw [stable_def, invariantU_def] "stable mutex invariantU";
by (constrains_tac 1);
qed "stable_invariantU";

Goalw [stable_def, invariantV_def] "stable mutex invariantV";
by (constrains_tac 1);
qed "stable_invariantV";

Goalw [MInit_def, invariantU_def] "MInit <= invariantU";
by Auto_tac;
qed "MInit_invariantU";

Goalw [MInit_def, invariantV_def] "MInit <= invariantV";
by Auto_tac;
qed "MInit_invariantV";

(*The intersection is an invariant of the system*)
Goal "reachable (MInit,mutex) <= invariantU Int invariantV";
by (simp_tac (simpset() addsimps
	      [strongest_invariant, Int_greatest, stable_Int, 
	       stable_invariantU, stable_invariantV, 
	       MInit_invariantU,MInit_invariantV]) 1); 
qed "reachable_subset_invariant";

val reachable_subset_invariant' = 
    rewrite_rule [invariantU_def, invariantV_def] reachable_subset_invariant;


(*The safety property (mutual exclusion) follows from the claimed invar_s*)
Goalw [invariantU_def, invariantV_def]
    "{s. MM s = 3 & NN s = 3} <= Compl (invariantU Int invariantV)";
by Auto_tac;
val lemma = result();

Goal "{s. MM s = 3 & NN s = 3} <= Compl (reachable (MInit,mutex))";
by (rtac ([lemma, reachable_subset_invariant RS Compl_anti_mono] 
	  MRS subset_trans) 1);
qed "mutual_exclusion";


(*The bad invariant FAILS in cmd1V*)
Goalw [stable_def, bad_invariantU_def] "stable mutex bad_invariantU";
by (constrains_tac 1);
by (REPEAT (trans_tac 1));
by (safe_tac (claset() addSEs [le_SucE]));
by (Asm_full_simp_tac 1);
(*Resulting state: n=1, p=false, m=4, u=false.  
  Execution of cmd1V (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
(*Check that subgoals remain: proof failed.*)
getgoal 1;  


(*** Progress for U ***)

Goalw [unless_def] "unless mutex {s. MM s=2} {s. MM s=3}";
by (constrains_tac 1);
qed "U_F0";

Goal "LeadsTo(MInit,mutex) {s. MM s=1} {s. PP s = VV s & MM s = 2}";
by (ensures_tac "cmd1U" 1);
qed "U_F1";

Goal "LeadsTo(MInit,mutex) {s. ~ PP s & MM s = 2} {s. MM s = 3}";
by (cut_facts_tac [reachable_subset_invariant'] 1);
by (ensures_tac "cmd2U" 1);
qed "U_F2";

Goalw [mutex_def] "LeadsTo(MInit,mutex) {s. MM s = 3} {s. PP s}";
by (rtac leadsTo_imp_LeadsTo 1); 
by (res_inst_tac [("B", "{s. MM s = 4}")] leadsTo_Trans 1);
by (ensures_tac "cmd4U" 2);
by (ensures_tac "cmd3U" 1);
qed "U_F3";

Goal "LeadsTo(MInit,mutex) {s. MM s = 2} {s. PP s}";
by (rtac ([LeadsTo_weaken_L, subset_refl RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val lemma2 = result();

Goal "LeadsTo(MInit,mutex) {s. MM s = 1} {s. PP s}";
by (rtac ([U_F1 RS LeadsTo_weaken_R, lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val lemma1 = result();


Goal "LeadsTo(MInit,mutex) {s. 1 <= MM s & MM s <= 3} {s. PP s}";
by (simp_tac (simpset() addsimps [le_Suc_eq, conj_disj_distribL] 
	                addcongs [rev_conj_cong]) 1);
by (simp_tac (simpset() addsimps [Collect_disj_eq, LeadsTo_Un_distrib,
				  lemma1, lemma2, U_F3] ) 1);
val lemma123 = result();


(*Misra's F4*)
Goal "LeadsTo(MInit,mutex) {s. UU s} {s. PP s}";
by (rtac LeadsTo_weaken_L 1);
by (rtac lemma123 1);
by (cut_facts_tac [reachable_subset_invariant'] 1);
by Auto_tac;
qed "u_leadsto_p";


(*** Progress for V ***)


Goalw [unless_def] "unless mutex {s. NN s=2} {s. NN s=3}";
by (constrains_tac 1);
qed "V_F0";

Goal "LeadsTo(MInit,mutex) {s. NN s=1} {s. PP s = (~ UU s) & NN s = 2}";
by (ensures_tac "cmd1V" 1);
qed "V_F1";

Goal "LeadsTo(MInit,mutex) {s. PP s & NN s = 2} {s. NN s = 3}";
by (cut_facts_tac [reachable_subset_invariant'] 1);
by (ensures_tac "cmd2V" 1);
qed "V_F2";

Goalw [mutex_def] "LeadsTo(MInit,mutex) {s. NN s = 3} {s. ~ PP s}";
by (rtac leadsTo_imp_LeadsTo 1); 
by (res_inst_tac [("B", "{s. NN s = 4}")] leadsTo_Trans 1);
by (ensures_tac "cmd4V" 2);
by (ensures_tac "cmd3V" 1);
qed "V_F3";

Goal "LeadsTo(MInit,mutex) {s. NN s = 2} {s. ~ PP s}";
by (rtac ([LeadsTo_weaken_L, subset_refl RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([V_F2, V_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val lemma2 = result();

Goal "LeadsTo(MInit,mutex) {s. NN s = 1} {s. ~ PP s}";
by (rtac ([V_F1 RS LeadsTo_weaken_R, lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val lemma1 = result();


Goal "LeadsTo(MInit,mutex) {s. 1 <= NN s & NN s <= 3} {s. ~ PP s}";
by (simp_tac (simpset() addsimps [le_Suc_eq, conj_disj_distribL] 
	                addcongs [rev_conj_cong]) 1);
by (simp_tac (simpset() addsimps [Collect_disj_eq, LeadsTo_Un_distrib,
				  lemma1, lemma2, V_F3] ) 1);
val lemma123 = result();


(*Misra's F4*)
Goal "LeadsTo(MInit,mutex) {s. VV s} {s. ~ PP s}";
by (rtac LeadsTo_weaken_L 1);
by (rtac lemma123 1);
by (cut_facts_tac [reachable_subset_invariant'] 1);
by Auto_tac;
qed "v_leadsto_not_p";


(** Absence of starvation **)

(*Misra's F6*)
Goal "LeadsTo(MInit,mutex) {s. MM s = 1} {s. MM s = 3}";
by (rtac LeadsTo_Un_duplicate 1);
by (rtac LeadsTo_cancel2 1);
by (rtac U_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac LeadsTo_Un_duplicate 1);
by (rtac ([v_leadsto_not_p, U_F0] MRS R_PSP_unless RSN(2, LeadsTo_cancel2)) 1);
by (rtac (U_F1 RS LeadsTo_weaken_R) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "m1_leadsto_3";


(*The same for V*)
Goal "LeadsTo(MInit,mutex) {s. NN s = 1} {s. NN s = 3}";
by (rtac LeadsTo_Un_duplicate 1);
by (rtac LeadsTo_cancel2 1);
by (rtac V_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac LeadsTo_Un_duplicate 1);
by (rtac ([u_leadsto_p, V_F0] MRS R_PSP_unless  RSN(2, LeadsTo_cancel2)) 1);
by (rtac (V_F1 RS LeadsTo_weaken_R) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "n1_leadsto_3";
