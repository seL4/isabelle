(*  Title:      ZF/ex/Primrec
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Primitive Recursive Functions: preliminary definitions
*)

(*Theory TF redeclares map_type*)
val map_type = thm "List.map_type";

(** Useful special cases of evaluation ***)

Goalw [SC_def] "[| x \\<in> nat;  l \\<in> list(nat) |] ==> SC ` (Cons(x,l)) = succ(x)";
by (Asm_simp_tac 1);
qed "SC";

Goalw [CONST_def] "[| l \\<in> list(nat) |] ==> CONST(k) ` l = k";
by (Asm_simp_tac 1);
qed "CONST";

Goalw [PROJ_def] "[| x \\<in> nat;  l \\<in> list(nat) |] ==> PROJ(0) ` (Cons(x,l)) = x";
by (Asm_simp_tac 1);
qed "PROJ_0";

Goalw [COMP_def] "[| l \\<in> list(nat) |] ==> COMP(g,[f]) ` l = g` [f`l]";
by (Asm_simp_tac 1);
qed "COMP_1";

Goalw [PREC_def] "l \\<in> list(nat) ==> PREC(f,g) ` (Cons(0,l)) = f`l";
by (Asm_simp_tac 1);
qed "PREC_0";

Goalw [PREC_def]
    "[| x \\<in> nat;  l \\<in> list(nat) |] ==>  \
\         PREC(f,g) ` (Cons(succ(x),l)) = \
\         g ` Cons(PREC(f,g)`(Cons(x,l)), Cons(x,l))";
by (Asm_simp_tac 1);
qed "PREC_succ";

