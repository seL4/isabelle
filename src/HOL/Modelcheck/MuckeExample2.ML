(*  Title:      HOL/Modelcheck/MuckeExample2.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)


(* prints the mucke output on the screen *)
(* trace_mc := true; *)
val Reach_rws = [Init_def,R_def,Reach_def,Reach2_def];

Goal "Reach2 True";
by (simp_tac (Mucke_ss addsimps Reach_rws) 1);
by (mc_mucke_tac [] 1);
qed "Reach_thm";

(*alternative:*)
goal thy "Reach2 True";
by (mc_mucke_tac Reach_rws 1);
qed "Reach_thm'";
