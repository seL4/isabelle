(*  Title:      HOLCF/IOA/meta_theory/Simulations.ML
    ID:         $Id$
    Author:     Olaf Müller

Simulations in HOLCF/IOA.
*)



Goal "(A~={}) = (? x. x:A)";
by (safe_tac set_cs);
by Auto_tac;
qed"set_non_empty";

Goal "(A Int B ~= {}) = (? x. x: A & x:B)";
by (simp_tac (simpset() addsimps [set_non_empty]) 1);
qed"Int_non_empty";


Goalw [Image_def]
"(R``{x} Int S ~= {}) = (? y. (x,y):R & y:S)";
by (simp_tac (simpset() addsimps [Int_non_empty]) 1);
qed"Sim_start_convert";

Addsimps [Sim_start_convert];


Goalw [is_ref_map_def,is_simulation_def]
"!! f. is_ref_map f C A ==> is_simulation {p. (snd p) = f (fst p)} C A";
by (Asm_full_simp_tac 1);
qed"ref_map_is_simulation";




