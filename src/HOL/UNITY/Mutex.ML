(*  Title:      HOL/UNITY/Mutex.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

open Mutex;

val cmd_defs = [mutex_def, cmd0_def, cmd1u_def, cmd1v_def, 
		cmd2_def, cmd3_def, cmd4_def];

goalw thy [mutex_def] "id : mutex";
by (Simp_tac 1);
qed "id_in_mutex";
AddIffs [id_in_mutex];


(** Constrains/Ensures tactics: NEED TO BE GENERALIZED OVER ALL PROGRAMS **)

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
      (EVERY [REPEAT (resolve_tac [LeadsTo_Basis, leadsTo_Basis, ensuresI] 1),
	      res_inst_tac [("act", sact)] transient_mem 2,
	      Simp_tac 2,
	      constrains_tac 1,
	      rewrite_goals_tac cmd_defs,
	      Auto_tac]);


(*The booleans p, u, v are always either 0 or 1*)
goalw thy [stable_def, boolVars_def]
    "stable mutex boolVars";
by (constrains_tac 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "stable_boolVars";

goal thy "reachable MInit mutex <= boolVars";
by (rtac strongest_invariant 1);
by (rtac stable_boolVars 2);
by (rewrite_goals_tac [MInit_def, boolVars_def]);
by Auto_tac;
qed "reachable_subset_boolVars";

val reachable_subset_boolVars' = 
    rewrite_rule [boolVars_def] reachable_subset_boolVars;

goalw thy [stable_def, invariant_def]
    "stable mutex (invariant 0 UU MM)";
by (constrains_tac 1);
qed "stable_invar_0um";

goalw thy [stable_def, invariant_def]
    "stable mutex (invariant 1 VV NN)";
by (constrains_tac 1);
qed "stable_invar_1vn";

goalw thy [MInit_def, invariant_def] "MInit <= invariant 0 UU MM";
by Auto_tac;
qed "MInit_invar_0um";

goalw thy [MInit_def, invariant_def] "MInit <= invariant 1 VV NN";
by Auto_tac;
qed "MInit_invar_1vn";

(*The intersection is an invariant of the system*)
goal thy "reachable MInit mutex <= invariant 0 UU MM Int invariant 1 VV NN";
by (simp_tac (simpset() addsimps
	      [strongest_invariant, Int_greatest, stable_Int, 
	       stable_invar_0um, stable_invar_1vn, 
	       MInit_invar_0um,MInit_invar_1vn]) 1); 
qed "reachable_subset_invariant";

val reachable_subset_invariant' = 
    rewrite_rule [invariant_def] reachable_subset_invariant;


(*The safety property (mutual exclusion) follows from the claimed invar_s*)
goalw thy [invariant_def]
    "{s. s MM = 3 & s NN = 3} <= \
\    Compl (invariant 0 UU MM Int invariant 1 VV NN)";
by Auto_tac;
val lemma = result();

goal thy "{s. s MM = 3 & s NN = 3} <= Compl (reachable MInit mutex)";
by (rtac ([lemma, reachable_subset_invariant RS Compl_anti_mono] MRS subset_trans) 1);
qed "mutual_exclusion";


(*The bad invariant FAILS in cmd1v*)
goalw thy [stable_def, bad_invariant_def]
    "stable mutex (bad_invariant 0 UU MM)";
by (constrains_tac 1);
by (trans_tac 1);
by (safe_tac (claset() addSEs [le_SucE]));
by (Asm_full_simp_tac 1);
(*Resulting state: n=1, p=false, m=4, u=false.  
  Execution of cmd1v (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
(*Check that subgoals remain: proof failed.*)
getgoal 1;  


(*** Progress for U ***)

goalw thy [unless_def] "unless mutex {s. s MM=2} {s. s MM=3}";
by (constrains_tac 1);
qed "U_F0";

goal thy "LeadsTo MInit mutex {s. s MM=1} {s. s PP = s VV & s MM = 2}";
by (rtac leadsTo_imp_LeadsTo 1);   (*makes the proof much faster*)
by (ensures_tac "cmd1u" 1);
qed "U_F1";

goal thy "LeadsTo MInit mutex {s. s PP = 0 & s MM = 2} {s. s MM = 3}";
by (cut_facts_tac [reachable_subset_invariant'] 1);
by (ensures_tac "cmd2 0 MM" 1);
qed "U_F2";

goalw thy [mutex_def] "LeadsTo MInit mutex {s. s MM = 3} {s. s PP = 1}";
by (rtac leadsTo_imp_LeadsTo 1); 
by (res_inst_tac [("B", "{s. s MM = 4}")] leadsTo_Trans 1);
by (ensures_tac "cmd4 1 MM" 2);
by (ensures_tac "cmd3 UU MM" 1);
qed "U_F3";

goal thy "LeadsTo MInit mutex {s. s MM = 2} {s. s PP = 1}";
by (rtac ([LeadsTo_weaken_L, subset_refl RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by (cut_facts_tac [reachable_subset_boolVars'] 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val lemma2 = result();

goal thy "LeadsTo MInit mutex {s. s MM = 1} {s. s PP = 1}";
by (rtac ([U_F1 RS LeadsTo_weaken_R, lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val lemma1 = result();


goal thy "LeadsTo MInit mutex {s. 1 <= s MM & s MM <= 3} {s. s PP = 1}";
by (simp_tac (simpset() addsimps [le_Suc_eq, conj_disj_distribL] 
	                addcongs [rev_conj_cong]) 1);
by (simp_tac (simpset() addsimps [Collect_disj_eq, LeadsTo_Un_distrib,
				  lemma1, lemma2, U_F3] ) 1);
val lemma123 = result();


(*Misra's F4*)
goal thy "LeadsTo MInit mutex {s. s UU = 1} {s. s PP = 1}";
by (rtac LeadsTo_weaken_L 1);
by (rtac lemma123 1);
by (cut_facts_tac [reachable_subset_invariant'] 1);
by Auto_tac;
qed "u_leadsto_p";


(*** Progress for V ***)


goalw thy [unless_def] "unless mutex {s. s NN=2} {s. s NN=3}";
by (constrains_tac 1);
qed "V_F0";

goal thy "LeadsTo MInit mutex {s. s NN=1} {s. s PP = 1 - s UU & s NN = 2}";
by (rtac leadsTo_imp_LeadsTo 1);   (*makes the proof much faster*)
by (ensures_tac "cmd1v" 1);
qed "V_F1";

goal thy "LeadsTo MInit mutex {s. s PP = 1 & s NN = 2} {s. s NN = 3}";
by (cut_facts_tac [reachable_subset_invariant'] 1);
by (ensures_tac "cmd2 1 NN" 1);
qed "V_F2";

goalw thy [mutex_def] "LeadsTo MInit mutex {s. s NN = 3} {s. s PP = 0}";
by (rtac leadsTo_imp_LeadsTo 1); 
by (res_inst_tac [("B", "{s. s NN = 4}")] leadsTo_Trans 1);
by (ensures_tac "cmd4 0 NN" 2);
by (ensures_tac "cmd3 VV NN" 1);
qed "V_F3";

goal thy "LeadsTo MInit mutex {s. s NN = 2} {s. s PP = 0}";
by (rtac ([LeadsTo_weaken_L, subset_refl RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([V_F2, V_F3] MRS LeadsTo_Trans) 1);
by (cut_facts_tac [reachable_subset_boolVars'] 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val lemma2 = result();

goal thy "LeadsTo MInit mutex {s. s NN = 1} {s. s PP = 0}";
by (rtac ([V_F1 RS LeadsTo_weaken_R, lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val lemma1 = result();


goal thy "LeadsTo MInit mutex {s. 1 <= s NN & s NN <= 3} {s. s PP = 0}";
by (simp_tac (simpset() addsimps [le_Suc_eq, conj_disj_distribL] 
	                addcongs [rev_conj_cong]) 1);
by (simp_tac (simpset() addsimps [Collect_disj_eq, LeadsTo_Un_distrib,
				  lemma1, lemma2, V_F3] ) 1);
val lemma123 = result();


(*Misra's F4*)
goal thy "LeadsTo MInit mutex {s. s VV = 1} {s. s PP = 0}";
by (rtac LeadsTo_weaken_L 1);
by (rtac lemma123 1);
by (cut_facts_tac [reachable_subset_invariant'] 1);
by Auto_tac;
qed "v_leadsto_not_p";


(** Absence of starvation **)

(*Misra's F6*)
goal thy "LeadsTo MInit mutex {s. s MM = 1} {s. s MM = 3}";
by (rtac LeadsTo_Un_duplicate 1);
by (rtac LeadsTo_cancel2 1);
by (rtac U_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac LeadsTo_Un_duplicate 1);
by (rtac ([v_leadsto_not_p, U_F0] MRS R_PSP_unless  RSN(2, LeadsTo_cancel2)) 1);
by (rtac (U_F1 RS LeadsTo_weaken_R) 1);
by (cut_facts_tac [reachable_subset_boolVars'] 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "m1_leadsto_3";


(*The same for V*)
goal thy "LeadsTo MInit mutex {s. s NN = 1} {s. s NN = 3}";
by (rtac LeadsTo_Un_duplicate 1);
by (rtac LeadsTo_cancel2 1);
by (rtac V_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac LeadsTo_Un_duplicate 1);
by (rtac ([u_leadsto_p, V_F0] MRS R_PSP_unless  RSN(2, LeadsTo_cancel2)) 1);
by (rtac (V_F1 RS LeadsTo_weaken_R) 1);
by (cut_facts_tac [reachable_subset_boolVars'] 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
qed "n1_leadsto_3";
