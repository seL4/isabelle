(*  Title:      HOLCF/IOA/meta_theory/LiveIOA.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Live I/O Automata

*)   

Delsimps [split_paired_Ex];

goalw thy [live_implements_def] 
"!! A. [| live_implements (A,LA) (B,LB); live_implements (B,LB) (C,LC) |] \
\     ==> live_implements (A,LA) (C,LC)"; 
auto();
qed"live_implements_trans";


section "Correctness of live refmap";
	

(* ---------------------------------------------------------------- *)
(*                Correctness of live refmap                        *)
(* ---------------------------------------------------------------- *)


goal thy "!! f. [| inp(C)=inp(A); out(C)=out(A); \
\                  is_live_ref_map f (C,M) (A,L) |] \
\               ==> live_implements (C,M) (A,L)";

by (asm_full_simp_tac (simpset() addsimps [is_live_ref_map_def, live_implements_def,
livetraces_def,liveexecutions_def]) 1);
by (safe_tac set_cs);
by (res_inst_tac[("x","corresp_ex A f ex")] exI 1);
by (safe_tac set_cs);
  (* Traces coincide, Lemma 1 *)
  by (pair_tac "ex" 1);
  by (etac (lemma_1 RS spec RS mp) 1);
  by (simp_tac (simpset() addsimps [externals_def])1);
  by (SELECT_GOAL (auto_tac (claset(),simpset()))1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def,reachable.reachable_0]) 1);
 
  (* corresp_ex is execution, Lemma 2 *)
  by (pair_tac "ex" 1);
  by (asm_full_simp_tac (simpset() addsimps [executions_def]) 1);
  (* start state *) 
  by (rtac conjI 1);
  by (asm_full_simp_tac (simpset() addsimps [is_ref_map_def,corresp_ex_def]) 1);
  (* is-execution-fragment *)
  by (etac (lemma_2 RS spec RS mp) 1);
  by (asm_full_simp_tac (simpset() addsimps [reachable.reachable_0]) 1);

 (* Liveness *)
auto();
qed"live_implements";


(*

(* Classical Fairness and Fairness by Temporal Formula coincide *)
 
goal thy "!! ex. Finite (snd ex) ==> \
\          (ex |== WF A acts) = (~ Enabled A acts (laststate ex))";

In 3 steps:

1) []<>P and <>[]P mean both P (Last`s)
2) Transform this to executions and laststate
3) plift is used to show that plift (laststate ex) : acts == False. 



*)