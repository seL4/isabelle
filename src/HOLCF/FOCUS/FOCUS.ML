(*  Title: 	HOLCF/FOCUS/FOCUS.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

open FOCUS;

val ex_eqI = prove_goal thy "? xx. x = xx" (K [Auto_tac]);
val ex2_eqI = prove_goal thy "? xx yy. x = xx & y = yy" (K [Auto_tac]);
val eq_UU_symf = prove_goal thy "(UU = f x) = (f x = UU)" (K [Auto_tac]);

AddSIs [ex_eqI, ex2_eqI];
Addsimps[eq_UU_symf];
Goal "(#x ~= 0) = (? a y. x = a~> y)";
by (simp_tac (simpset() addsimps [slen_empty_eq, fstream_exhaust_eq]) 1);
qed "fstream_exhaust_slen_eq";

Addsimps[slen_less_1_eq, fstream_exhaust_slen_eq,
		   slen_fscons_eq, slen_fscons_less_eq];
Addsimps[thm "Suc_ile_eq"];
AddEs  [strictI];
