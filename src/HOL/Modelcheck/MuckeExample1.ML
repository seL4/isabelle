(*  Title:      HOL/Modelcheck/MuckeExample1.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

val reach_rws = [INIT_def,N_def,reach_def];

Goal "reach (True,True,True)";
by (simp_tac (Mucke_ss addsimps reach_rws) 1); 
by (mc_mucke_tac [] 1);
qed "reach_ex_thm1";

(*alternative*)
Goal "reach (True,True,True)";
by (mc_mucke_tac reach_rws 1);
qed "reach_ex_thm1'";
