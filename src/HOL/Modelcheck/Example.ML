(*  Title:      HOL/Modelcheck/Example.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

val reach_rws = [reach_def,INIT_def,N_def];


goal thy "reach (True,True,True)";
by (simp_tac (MC_ss addsimps reach_rws) 1);

(*show the current proof state using the model checker syntax*)
setmp print_mode ["Eindhoven"] pr ();

(* actually invoke the model checker *)
(* try out after installing the model checker: see the README file *)

(* by (mc_tac 1); *)

(*qed "reach_ex_thm1";*)



