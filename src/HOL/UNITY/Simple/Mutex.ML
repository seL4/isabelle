(*  Title:      HOL/UNITY/Mutex
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra
*)

Addsimps [Mutex_def RS def_prg_Init];
program_defs_ref := [Mutex_def];

Addsimps (map simp_of_act
	  [U0_def, U1_def, U2_def, U3_def, U4_def, 
	   V0_def, V1_def, V2_def, V3_def, V4_def]);

Addsimps (map simp_of_set [IU_def, IV_def, bad_IU_def]);


Goal "Mutex : Always IU";
by (always_tac 1);
qed "IU";

Goal "Mutex : Always IV";
by (always_tac 1);
qed "IV";

(*The safety property: mutual exclusion*)
Goal "Mutex : Always {s. ~ (m s = #3 & n s = #3)}";
by (rtac ([IU, IV] MRS Always_Int_I RS Always_weaken) 1);
by Auto_tac;
qed "mutual_exclusion";


(*The bad invariant FAILS in V1*)
Goal "Mutex : Always bad_IU";
by (always_tac 1);
by Auto_tac;
(*Resulting state: n=1, p=false, m=4, u=false.  
  Execution of V1 (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
(*Check that subgoals remain: proof failed.*)
getgoal 1;  


Goal "((#1::int) <= i & i <= #3) = (i = #1 | i = #2 | i = #3)";
by (arith_tac 1);
qed "eq_123";


(*** Progress for U ***)

Goalw [Unless_def] "Mutex : {s. m s=#2} Unless {s. m s=#3}";
by (constrains_tac 1);
qed "U_F0";

Goal "Mutex : {s. m s=#1} LeadsTo {s. p s = v s & m s = #2}";
by (ensures_tac "U1" 1);
qed "U_F1";

Goal "Mutex : {s. ~ p s & m s = #2} LeadsTo {s. m s = #3}";
by (cut_facts_tac [IU] 1);
by (ensures_tac "U2" 1);
qed "U_F2";

Goal "Mutex : {s. m s = #3} LeadsTo {s. p s}";
by (res_inst_tac [("B", "{s. m s = #4}")] LeadsTo_Trans 1);
by (ensures_tac "U4" 2);
by (ensures_tac "U3" 1);
qed "U_F3";

Goal "Mutex : {s. m s = #2} LeadsTo {s. p s}";
by (rtac ([LeadsTo_weaken_L, Int_lower2 RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val U_lemma2 = result();

Goal "Mutex : {s. m s = #1} LeadsTo {s. p s}";
by (rtac ([U_F1 RS LeadsTo_weaken_R, U_lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val U_lemma1 = result();

Goal "Mutex : {s. #1 <= m s & m s <= #3} LeadsTo {s. p s}";
by (simp_tac (simpset() addsimps [eq_123, Collect_disj_eq, LeadsTo_Un_distrib,
				  U_lemma1, U_lemma2, U_F3] ) 1);
val U_lemma123 = result();

(*Misra's F4*)
Goal "Mutex : {s. u s} LeadsTo {s. p s}";
by (rtac ([IU, U_lemma123] MRS Always_LeadsTo_weaken) 1);
by Auto_tac;
qed "u_Leadsto_p";


(*** Progress for V ***)


Goalw [Unless_def] "Mutex : {s. n s=#2} Unless {s. n s=#3}";
by (constrains_tac 1);
qed "V_F0";

Goal "Mutex : {s. n s=#1} LeadsTo {s. p s = (~ u s) & n s = #2}";
by (ensures_tac "V1" 1);
qed "V_F1";

Goal "Mutex : {s. p s & n s = #2} LeadsTo {s. n s = #3}";
by (cut_facts_tac [IV] 1);
by (ensures_tac "V2" 1);
qed "V_F2";

Goal "Mutex : {s. n s = #3} LeadsTo {s. ~ p s}";
by (res_inst_tac [("B", "{s. n s = #4}")] LeadsTo_Trans 1);
by (ensures_tac "V4" 2);
by (ensures_tac "V3" 1);
qed "V_F3";

Goal "Mutex : {s. n s = #2} LeadsTo {s. ~ p s}";
by (rtac ([LeadsTo_weaken_L, Int_lower2 RS subset_imp_LeadsTo] 
	  MRS LeadsTo_Diff) 1);
by (rtac ([V_F2, V_F3] MRS LeadsTo_Trans) 1);
by (auto_tac (claset() addSEs [less_SucE], simpset()));
val V_lemma2 = result();

Goal "Mutex : {s. n s = #1} LeadsTo {s. ~ p s}";
by (rtac ([V_F1 RS LeadsTo_weaken_R, V_lemma2] MRS LeadsTo_Trans) 1);
by (Blast_tac 1);
val V_lemma1 = result();

Goal "Mutex : {s. #1 <= n s & n s <= #3} LeadsTo {s. ~ p s}";
by (simp_tac (simpset() addsimps [eq_123, Collect_disj_eq, LeadsTo_Un_distrib,
				  V_lemma1, V_lemma2, V_F3] ) 1);
val V_lemma123 = result();


(*Misra's F4*)
Goal "Mutex : {s. v s} LeadsTo {s. ~ p s}";
by (rtac ([IV, V_lemma123] MRS Always_LeadsTo_weaken) 1);
by Auto_tac;
qed "v_Leadsto_not_p";


(** Absence of starvation **)

(*Misra's F6*)
Goal "Mutex : {s. m s = #1} LeadsTo {s. m s = #3}";
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac U_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac ([v_Leadsto_not_p, U_F0] MRS PSP_Unless) 2);
by (rtac (U_F1 RS LeadsTo_weaken_R) 1);
by Auto_tac;
qed "m1_Leadsto_3";

(*The same for V*)
Goal "Mutex : {s. n s = #1} LeadsTo {s. n s = #3}";
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac V_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac ([u_Leadsto_p, V_F0] MRS PSP_Unless) 2);
by (rtac (V_F1 RS LeadsTo_weaken_R) 1);
by Auto_tac;
qed "n1_Leadsto_3";
