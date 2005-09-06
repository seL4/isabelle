(*  Title:      HOLCF/FOCUS/FOCUS.ML
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen
*)

val ex_eqI = prove_goal (the_context ()) "? xx. x = xx" (K [Auto_tac]);
val ex2_eqI = prove_goal (the_context ()) "? xx yy. x = xx & y = yy" (K [Auto_tac]);
val eq_UU_symf = prove_goal (the_context ()) "(UU = f x) = (f x = UU)" (K [Auto_tac]);

AddSIs [ex_eqI, ex2_eqI];
Addsimps[eq_UU_symf];
Goal "(#x ~= 0) = (? a y. x = a~> y)";
by (simp_tac (simpset() addsimps [thm "slen_empty_eq", fstream_exhaust_eq]) 1);
qed "fstream_exhaust_slen_eq";

Addsimps[thm "slen_less_1_eq", fstream_exhaust_slen_eq,
                   thm "slen_fscons_eq", thm "slen_fscons_less_eq"];
Addsimps[thm "Suc_ile_eq"];
AddEs  [strictI];
