(*  Title:      HOL/Datatype.ML
    ID:         $Id$
    Author:     Stefan Berghofer
    Copyright   1999  TU Muenchen
*)

(** sum_case -- the selection operator for sums **)

(*compatibility*)
val [sum_case_Inl, sum_case_Inr] = sum.cases;
bind_thm ("sum_case_Inl", sum_case_Inl);
bind_thm ("sum_case_Inr", sum_case_Inr);

Goal "sum_case (%x::'a. f(Inl x)) (%y::'b. f(Inr y)) s = f(s)";
by (EVERY1 [res_inst_tac [("s","s")] sumE, 
            etac ssubst, rtac sum_case_Inl,
            etac ssubst, rtac sum_case_Inr]);
qed "surjective_sum";

(*Prevents simplification of f and g: much faster*)
Goal "s=t ==> sum_case f g s = sum_case f g t";
by (etac arg_cong 1);
qed "sum_case_weak_cong";

val [p1,p2] = Goal
  "[| sum_case f1 f2 = sum_case g1 g2;  \
\     [| f1 = g1; f2 = g2 |] ==> P |] \
\  ==> P";
by (rtac p2 1);
by (rtac ext 1);
by (cut_inst_tac [("x","Inl x")] (p1 RS fun_cong) 1);
by (Asm_full_simp_tac 1);
by (rtac ext 1);
by (cut_inst_tac [("x","Inr x")] (p1 RS fun_cong) 1);
by (Asm_full_simp_tac 1);
qed "sum_case_inject";
