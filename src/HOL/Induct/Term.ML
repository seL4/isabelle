(*  Title:      HOL/Induct/Term.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   1998  TU Muenchen

Terms over a given alphabet -- function applications
*)

(** a simple theorem about composition of substitutions **)

Goal "(subst_term ((subst_term f1) o f2) t) =  \
  \  (subst_term f1 (subst_term f2 t)) &  \
  \  (subst_term_list ((subst_term f1) o f2) ts) =  \
  \  (subst_term_list f1 (subst_term_list f2 ts))";
by (induct_tac "t ts" 1);
by (ALLGOALS Asm_full_simp_tac);
qed "subst_comp";

(**** alternative induction rule ****)

bind_thm ("term_induct2", prove_goal thy
  "[| !!v. P (Var v);  \
   \  !!f ts. list_all P ts ==> P (App f ts) |] ==>  \
   \    P t & list_all P ts"
  (fn prems =>
    [induct_tac "t ts" 1,
     resolve_tac prems 1,
     resolve_tac prems 1,
     atac 1,
     ALLGOALS Asm_simp_tac]) RS conjunct1);
