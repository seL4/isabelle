(*  Title:      ZF/UNITY/Mutex.ML
    ID:         $Id \\<in> Mutex.ML,v 1.4 2003/05/27 09:39:05 paulson Exp $
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Based on "A Family of 2-Process Mutual Exclusion Algorithms" by J Misra

Variables' types are introduced globally so that type verification
reduces to the usual ZF typechecking \\<in> an ill-tyed expression will
reduce to the empty set.

*)

(** Variables' types **)

Addsimps  [p_type, u_type, v_type, m_type, n_type];

Goalw [state_def] "s \\<in> state ==>s`u \\<in> bool";
by (dres_inst_tac [("a", "u")] apply_type 1);
by Auto_tac;
qed "u_value_type";

Goalw [state_def] "s \\<in> state ==> s`v \\<in> bool";
by (dres_inst_tac [("a", "v")] apply_type 1);
by Auto_tac;
qed "v_value_type";

Goalw [state_def] "s \\<in> state ==> s`p \\<in> bool";
by (dres_inst_tac [("a", "p")] apply_type 1);
by Auto_tac;
qed "p_value_type";

Goalw [state_def] "s \\<in> state ==> s`m \\<in> int";
by (dres_inst_tac [("a", "m")] apply_type 1);
by Auto_tac;
qed "m_value_type";

Goalw [state_def] "s \\<in> state ==>s`n \\<in> int";
by (dres_inst_tac [("a", "n")] apply_type 1);
by Auto_tac;
qed "n_value_type";

Addsimps [p_value_type, u_value_type, v_value_type,
          m_value_type, n_value_type];
AddTCs [p_value_type, u_value_type, v_value_type,
          m_value_type, n_value_type];
(** Mutex is a program **)

Goalw [Mutex_def] "Mutex \\<in> program";
by Auto_tac;
qed "Mutex_in_program";
Addsimps [Mutex_in_program];
AddTCs [Mutex_in_program];

Addsimps [Mutex_def RS def_prg_Init];
program_defs_ref := [Mutex_def];

Addsimps (map simp_of_act
          [U0_def, U1_def, U2_def, U3_def, U4_def, 
           V0_def, V1_def, V2_def, V3_def, V4_def]);

Addsimps (map simp_of_set [U0_def, U1_def, U2_def, U3_def, U4_def, 
           V0_def, V1_def, V2_def, V3_def, V4_def]);

Addsimps (map simp_of_set [IU_def, IV_def, bad_IU_def]);

Goal "Mutex \\<in> Always(IU)";
by (always_tac 1);
by Auto_tac;
qed "IU";

Goal "Mutex \\<in> Always(IV)";
by (always_tac 1);
qed "IV";

(*The safety property \\<in> mutual exclusion*)
Goal "Mutex \\<in> Always({s \\<in> state. ~(s`m = #3 & s`n = #3)})";
by (rtac ([IU, IV] MRS Always_Int_I RS Always_weaken) 1);
by Auto_tac;
qed "mutual_exclusion";

(*The bad invariant FAILS in V1*)

Goal "[| x$<#1; #3 $<= x |] ==> P";
by (dres_inst_tac [("j", "#1"), ("k", "#3")]  zless_zle_trans 1);
by (dres_inst_tac [("j", "x")]  zle_zless_trans 2);
by Auto_tac;
qed "less_lemma";

Goal "Mutex \\<in> Always(bad_IU)";
by (always_tac 1);
by (auto_tac (claset(), simpset() addsimps [not_zle_iff_zless]));
by (auto_tac (claset(), simpset() addsimps [bool_def]));
by (subgoal_tac "#1 $<= #3" 1);
by (dres_inst_tac [("x", "#1"), ("y", "#3")] zle_trans 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [not_zless_iff_zle RS iff_sym]) 1);
by Auto_tac;
(*Resulting state \\<in> n=1, p=false, m=4, u=false.  
  Execution of V1 (the command of process v guarded by n=1) sets p:=true,
  violating the invariant!*)
(*Check that subgoals remain \\<in> proof failed.*)
getgoal 1;


(*** Progress for U ***)

Goalw [Unless_def] 
"Mutex \\<in> {s \\<in> state. s`m=#2} Unless {s \\<in> state. s`m=#3}";
by (constrains_tac 1);
qed "U_F0";

Goal "Mutex \\<in> {s \\<in> state. s`m=#1} LeadsTo {s \\<in> state. s`p = s`v & s`m = #2}";
by (ensures_tac "U1" 1);
qed "U_F1";

Goal "Mutex \\<in> {s \\<in> state. s`p =0 & s`m = #2} LeadsTo {s \\<in> state. s`m = #3}";
by (cut_facts_tac [IU] 1);
by (ensures_tac "U2" 1);
qed "U_F2";

Goal "Mutex \\<in> {s \\<in> state. s`m = #3} LeadsTo {s \\<in> state. s`p=1}";
by (res_inst_tac [("B", "{s \\<in> state. s`m = #4}")] LeadsTo_Trans 1);
by (ensures_tac "U4" 2);
by (ensures_tac "U3" 1);
qed "U_F3";


Goal "Mutex \\<in> {s \\<in> state. s`m = #2} LeadsTo {s \\<in> state. s`p=1}";
by (rtac ([LeadsTo_weaken_L, Int_lower2 RS subset_imp_LeadsTo] 
          MRS LeadsTo_Diff) 1);
by (rtac ([U_F2, U_F3] MRS LeadsTo_Trans) 1);
by Auto_tac;
by (auto_tac (claset() addSDs [p_value_type], simpset() addsimps [bool_def]));
val U_lemma2 = result();

Goal "Mutex \\<in> {s \\<in> state. s`m = #1} LeadsTo {s \\<in> state. s`p =1}";
by (rtac ([U_F1 RS LeadsTo_weaken_R, U_lemma2] MRS LeadsTo_Trans) 1);
by Auto_tac;
val U_lemma1 = result();

Goal "i \\<in> int ==> (#1 $<= i & i $<= #3) <-> (i=#1 | i=#2 | i=#3)";
by Auto_tac;
by (auto_tac (claset(), simpset() addsimps [neq_iff_zless]));
by (dres_inst_tac [("j", "#3"), ("i", "i")] zle_zless_trans 4);
by (dres_inst_tac [("j", "i"), ("i", "#1")] zle_zless_trans 2);
by (dres_inst_tac [("j", "i"), ("i", "#1")] zle_zless_trans 1);
by Auto_tac;
by (rtac zle_anti_sym 1);
by (ALLGOALS(asm_simp_tac (simpset()
      addsimps [zless_add1_iff_zle RS iff_sym])));
qed "eq_123";


Goal "Mutex \\<in> {s \\<in> state. #1 $<= s`m & s`m $<= #3} LeadsTo {s \\<in> state. s`p=1}";
by (simp_tac (simpset() addsimps [m_value_type RS eq_123, Collect_disj_eq,
                                  LeadsTo_Un_distrib,
                                  U_lemma1, U_lemma2, U_F3] ) 1);
val U_lemma123 = result();


(*Misra's F4*)
Goal "Mutex \\<in> {s \\<in> state. s`u = 1} LeadsTo {s \\<in> state. s`p=1}";
by (rtac ([IU, U_lemma123] MRS Always_LeadsTo_weaken) 1);
by Auto_tac;
qed "u_Leadsto_p";


(*** Progress for V ***)

Goalw [Unless_def] 
"Mutex \\<in> {s \\<in> state. s`n=#2} Unless {s \\<in> state. s`n=#3}";
by (constrains_tac 1);
qed "V_F0";

Goal "Mutex \\<in> {s \\<in> state. s`n=#1} LeadsTo {s \\<in> state. s`p = not(s`u) & s`n = #2}";
by (ensures_tac "V1" 1);
qed "V_F1";

Goal "Mutex \\<in> {s \\<in> state. s`p=1 & s`n = #2} LeadsTo {s \\<in> state. s`n = #3}";
by (cut_facts_tac [IV] 1);
by (ensures_tac "V2" 1);
qed "V_F2";

Goal "Mutex \\<in> {s \\<in> state. s`n = #3} LeadsTo {s \\<in> state. s`p=0}";
by (res_inst_tac [("B", "{s \\<in> state. s`n = #4}")] LeadsTo_Trans 1);
by (ensures_tac "V4" 2);
by (ensures_tac "V3" 1);
qed "V_F3";

Goal "Mutex \\<in> {s \\<in> state. s`n = #2} LeadsTo {s \\<in> state. s`p=0}";
by (rtac ([LeadsTo_weaken_L, Int_lower2 RS subset_imp_LeadsTo] 
          MRS LeadsTo_Diff) 1);
by (rtac ([V_F2, V_F3] MRS LeadsTo_Trans) 1);
by Auto_tac;
by (auto_tac (claset() addSDs [p_value_type], simpset() addsimps [bool_def]));
val V_lemma2 = result();

Goal "Mutex \\<in> {s \\<in> state. s`n = #1} LeadsTo {s \\<in> state. s`p = 0}";
by (rtac ([V_F1 RS LeadsTo_weaken_R, V_lemma2] MRS LeadsTo_Trans) 1);
by Auto_tac;
val V_lemma1 = result();

Goal "Mutex \\<in> {s \\<in> state. #1 $<= s`n & s`n $<= #3} LeadsTo {s \\<in> state. s`p = 0}";
by (simp_tac (simpset() addsimps 
     [n_value_type RS eq_123, Collect_disj_eq, LeadsTo_Un_distrib,
                  V_lemma1, V_lemma2, V_F3] ) 1);
val V_lemma123 = result();

(*Misra's F4*)
Goal "Mutex \\<in> {s \\<in> state. s`v = 1} LeadsTo {s \\<in> state. s`p = 0}";
by (rtac ([IV, V_lemma123] MRS Always_LeadsTo_weaken) 1);
by Auto_tac;
qed "v_Leadsto_not_p";

(** Absence of starvation **)

(*Misra's F6*)
Goal "Mutex \\<in> {s \\<in> state. s`m = #1} LeadsTo {s \\<in> state. s`m = #3}";
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac U_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac ([v_Leadsto_not_p, U_F0] MRS PSP_Unless) 2);
by (rtac (U_F1 RS LeadsTo_weaken_R) 1);
by Auto_tac;
by (auto_tac (claset() addSDs [v_value_type], simpset() addsimps [bool_def]));
qed "m1_Leadsto_3";


(*The same for V*)
Goal "Mutex \\<in> {s \\<in> state. s`n = #1} LeadsTo {s \\<in> state. s`n = #3}";
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac V_F2 2);
by (simp_tac (simpset() addsimps [Collect_conj_eq] ) 1);
by (stac Un_commute 1);
by (rtac (LeadsTo_cancel2 RS LeadsTo_Un_duplicate) 1);
by (rtac ([u_Leadsto_p, V_F0] MRS PSP_Unless) 2);
by (rtac (V_F1 RS LeadsTo_weaken_R) 1);
by Auto_tac;
by (auto_tac (claset() addSDs [u_value_type], simpset() addsimps [bool_def]));
qed "n1_Leadsto_3";
