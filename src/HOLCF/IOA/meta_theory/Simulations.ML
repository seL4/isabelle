(*  Title:      HOLCF/IOA/meta_theory/Simulations.ML
    ID:         $Id$
    Author:     Olaf Mueller
    Copyright   1997  TU Muenchen

Simulations in HOLCF/IOA
*)



goal thy "(A~={}) = (? x. x:A)";
by (safe_tac set_cs);
auto();
qed"set_non_empty";

goal thy "(A Int B ~= {}) = (? x. x: A & x:B)";
by (simp_tac (simpset() addsimps [set_non_empty]) 1);
qed"Int_non_empty";


goalw thy [Image_def]
"(R^^{x} Int S ~= {}) = (? y. (x,y):R & y:S)";
by (simp_tac (simpset() addsimps [Int_non_empty]) 1);
qed"Sim_start_convert";

Addsimps [Sim_start_convert];


goalw thy [is_ref_map_def,is_simulation_def]
"!! f. is_ref_map f C A ==> is_simulation {p. (snd p) = f (fst p)} C A";
(* start states *)
by (Asm_full_simp_tac 1);
(* main case *)
by (Blast_tac 1);
qed"ref_map_is_simulation";




