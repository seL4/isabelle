(*  Title:      HOL/UNITY/TimerArray.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

A trivial example of reasoning about an array of processes
*)

Addsimps [Timer_def RS def_prg_Init];
program_defs_ref := [Timer_def];

Addsimps [count_def, decr_def];

(*Demonstrates induction, but not used in the following proof*)
Goal "Timer : UNIV leadsTo {s. count s = 0}";
by (res_inst_tac [("f", "count")] lessThan_induct 1);
by (Simp_tac 1);
by (case_tac "m" 1);
by (force_tac (claset() addSIs [subset_imp_leadsTo], simpset()) 1);
by (ensures_tac "decr" 1);
qed "Timer_leadsTo_zero";

Goal "Timer : preserves snd";
by (rtac preservesI 1);
by (constrains_tac 1);
qed "Timer_preserves_snd";
AddIffs [Timer_preserves_snd];


Goal "finite I \
\     ==> (plam i: I. Timer) : UNIV leadsTo {(s,uu). ALL i:I. s i = 0}";
by (eres_inst_tac [("A'1", "%i. lift_set i ({0} <*> UNIV)")]
    (finite_stable_completion RS leadsTo_weaken) 1);
by Auto_tac;
(*Safety property, already reduced to the single Timer case*)
by (constrains_tac 2);
(*Progress property for the array of Timers*)
by (res_inst_tac [("f", "sub i o fst")] lessThan_induct 1);
by (case_tac "m" 1);
(*Annoying need to massage the conditions to have the form (... <*> UNIV)*)
by (auto_tac (claset() addIs [subset_imp_leadsTo], 
	      simpset() addsimps [insert_absorb, lessThan_Suc RS sym,
				  lift_set_Un_distrib RS sym,
				  Times_Un_distrib1 RS sym,
				  Times_Diff_distrib1 RS sym]));
by (rename_tac "n" 1);
by (rtac PLam_leadsTo_Basis 1);
by (auto_tac (claset(), simpset() addsimps [lessThan_Suc RS sym]));
by (constrains_tac 1);
by (res_inst_tac [("act", "decr")] transientI 1);
by (auto_tac (claset(), simpset() addsimps [Timer_def]));
qed "TimerArray_leadsTo_zero";
