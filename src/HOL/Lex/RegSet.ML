(*  Title:      HOL/Lex/RegSet.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

AddIffs [star.NilI];
Addsimps [star.ConsI];
AddIs [star.ConsI];

Goal "(!xs: set xss. xs:S) --> concat xss : star S";
by (induct_tac "xss" 1);
by (ALLGOALS Asm_full_simp_tac);
qed_spec_mp "concat_in_star";

Goal
 "w : star U = (? us. (!u : set(us). u : U) & (w = concat us))";
by (rtac iffI 1);
 by (etac star.induct 1);
  by (res_inst_tac [("x","[]")] exI 1);
  by (Simp_tac 1);
 by (Clarify_tac 1);
 by (res_inst_tac [("x","a#us")] exI 1);
 by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (asm_simp_tac (simpset() addsimps [concat_in_star]) 1);
qed "in_star";
