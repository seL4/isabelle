(*  Title:      HOL/Induct/ABexp.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   1998  TU Muenchen

Arithmetic and boolean expressions
*)

(** substitution theorems for arithmetic and boolean expressions **)

(* One variable *)
Goal
  "evala env (substa (Var(v := a')) a) = evala (env(v := evala env a')) a &  \
 \ evalb env (substb (Var(v := a')) b) = evalb (env(v := evala env a')) b";
by (induct_tac "a b" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "subst1_aexp_bexp";

(* All variables *)
Goal
  "evala env (substa s a) = evala (%x. evala env (s x)) a &  \
 \ evalb env (substb s b) = evalb (%x. evala env (s x)) b";
by (induct_tac "a b" 1);
by (Auto_tac);
qed "subst_all_aexp_bexp";
