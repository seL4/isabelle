(*  Title:      HOL/Induct/ABexp.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   1998  TU Muenchen

Arithmetic and boolean expressions
*)

(** substitution theorem for arithmetic and boolean expressions **)

Goal
  "eval_aexp env (subst_aexp (Var(v := a')) a) = eval_aexp (env(v := eval_aexp env a')) a &  \
 \ eval_bexp env (subst_bexp (Var(v := a')) b) = eval_bexp (env(v := eval_aexp env a')) b";
by (mutual_induct_tac ["a","b"] 1);
by (ALLGOALS Asm_full_simp_tac);
qed "subst_aexp_bexp";
