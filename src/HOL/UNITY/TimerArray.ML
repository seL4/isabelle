(*  Title:      HOL/UNITY/TimerArray.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A trivial example of reasoning about an array of processes
*)

Addsimps [Timer_def RS def_prg_Init];
program_defs_ref := [Timer_def];

Addsimps [decr_def];

(*Demonstrates induction, but not used in the following proof*)
Goal "Timer : UNIV leadsTo {0}";
by (res_inst_tac [("f", "id")] (allI RS lessThan_induct) 1);
by (Simp_tac 1);
by (exhaust_tac "m" 1);
by (blast_tac (claset() addSIs [subset_imp_leadsTo]) 1);
by (ensures_tac "decr" 1);
qed "Timer_leadsTo_zero";

Goal "finite I ==> (plam i: I. Timer) : UNIV leadsTo {s. ALL i:I. s i = 0}";
by (eres_inst_tac [("A'1", "%i. lift_set i {0}")]
    (finite_stable_completion RS leadsTo_weaken) 1);
by Auto_tac;
by (constrains_tac 2);
by (res_inst_tac [("f", "sub i")] (allI RS lessThan_induct) 1);
by (exhaust_tac "m" 1);
by (auto_tac (claset() addIs [subset_imp_leadsTo], 
	      simpset() addsimps [insert_absorb, lessThan_Suc RS sym]));
by (rename_tac "n" 1);
by (rtac PLam_leadsTo_Basis 1);
by (auto_tac (claset(), simpset() addsimps [lessThan_Suc RS sym]));
by (constrains_tac 1);
by (res_inst_tac [("act", "decr")] transient_mem 1);
by (auto_tac (claset(), simpset() addsimps [Timer_def]));
qed "TimerArray_leadsTo_zero";
