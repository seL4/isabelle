(*  Title:      HOLCF/IOA/meta_theory/LiveIOA.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Live I/O Automata.
*)   

Delsimps [split_paired_Ex];

Goalw [live_implements_def] 
"!!LC. [| live_implements (A,LA) (B,LB); live_implements (B,LB) (C,LC) |] \
\     ==> live_implements (A,LA) (C,LC)"; 
by Auto_tac;
qed"live_implements_trans";


section "Correctness of live refmap";
	

(* ---------------------------------------------------------------- *)
(*                Correctness of live refmap                        *)
(* ---------------------------------------------------------------- *)


Goal "[| inp(C)=inp(A); out(C)=out(A); \
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
by Auto_tac;
qed"live_implements";
