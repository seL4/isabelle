(*  Title:      HOL/Modelcheck/MuckeExample1.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

val reach_rws = [INIT_def,N_def,reach_def];

(*
goal thy "reach (True,True,True)";
by (simp_tac (Mucke_ss addsimps reach_rws) 1); 
by (mc_mucke_tac thy [] 1);
qed "reach_ex_thm1";

(* Alternative: *)
goal thy "reach (True,True,True)";
by (mc_mucke_tac thy reach_rws 1);
qed "reach_ex_thm1";

*)

