(*  Title:      HOL/IOA/meta_theory/Solve.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Weak possibilities mapping (abstraction)
*)

open Solve;

val SS = SS addsimps [mk_behaviour_thm,trans_in_actions];

goalw Solve.thy [is_weak_pmap_def,behaviours_def]
  "!!f. [| IOA(C); IOA(A); externals(asig_of(C)) = externals(asig_of(A)); \
\          is_weak_pmap f C A |] ==> behaviours(C) <= behaviours(A)";

  by (simp_tac(SS addsimps [has_behaviour_def])1);
  by (safe_tac set_cs);

  (* give execution of abstract automata *)
  by (res_inst_tac[("x","<mk_behaviour A (fst ex),%i.f(snd ex i)>")] bexI 1);

  (* Behaviours coincide *)
  by (asm_simp_tac (SS addsimps [mk_behaviour_def,filter_oseq_idemp])1);

  (* Use lemma *)
  by (forward_tac [states_of_exec_reachable] 1);

  (* Now show that it's an execution *)
  by (asm_full_simp_tac(SS addsimps [executions_def]) 1);
  by (safe_tac set_cs);

  (* Start states map to start states *)
  by (dtac bspec 1);
  by (atac 1);

  (* Show that it's an execution fragment *)
  by (asm_full_simp_tac (SS addsimps [is_execution_fragment_def])1);
  by (safe_tac HOL_cs);

  by (eres_inst_tac [("x","snd ex n")] allE 1);
  by (eres_inst_tac [("x","snd ex (Suc n)")] allE 1);
  by (eres_inst_tac [("x","a")] allE 1);
  by (asm_full_simp_tac SS 1);
qed "trace_inclusion";
