(*  Title:      Terms.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

Addsimps ([lambda.dom_subset RS subsetD] @ lambda.intrs);


(* ------------------------------------------------------------------------- *)
(*        unmark lemmas                                                      *)
(* ------------------------------------------------------------------------- *)

Goal "u:redexes ==> unmark(u):lambda";
by (etac redexes.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "unmark_type";

Goal "u:lambda ==> unmark(u) = u";
by (etac lambda.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "lambda_unmark";


(* ------------------------------------------------------------------------- *)
(*         lift and subst preserve lambda                                    *)
(* ------------------------------------------------------------------------- *)

Goal "v:lambda ==> ALL k:nat. lift_rec(v,k):lambda";
by (etac lambda.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lift_rec_Var])));
bind_thm ("liftL_type", result() RS bspec);

Goal "v:lambda ==>  ALL n:nat. ALL u:lambda. subst_rec(u,v,n):lambda";
by (etac lambda.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [liftL_type,subst_Var])));
qed "substL_typea";
bind_thm ("substL_type", result() RS bspec RS bspec);


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

val red_typechecks = [substL_type]@nat_typechecks@lambda.intrs@bool_typechecks;
