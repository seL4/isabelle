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

Goal "u \\<in> redexes ==> unmark(u):lambda";
by (etac redexes.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "unmark_type";

Goal "u \\<in> lambda ==> unmark(u) = u";
by (etac lambda.induct 1);
by (ALLGOALS Asm_simp_tac);
qed "lambda_unmark";


(* ------------------------------------------------------------------------- *)
(*         lift and subst preserve lambda                                    *)
(* ------------------------------------------------------------------------- *)

Goal "v \\<in> lambda ==> \\<forall>k \\<in> nat. lift_rec(v,k):lambda";
by (etac lambda.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lift_rec_Var])));
qed_spec_mp "liftL_type";

Goal "v \\<in> lambda ==>  \\<forall>n \\<in> nat. \\<forall>u \\<in> lambda. subst_rec(u,v,n):lambda";
by (etac lambda.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [liftL_type,subst_Var])));
qed_spec_mp "substL_type";


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

val red_typechecks = [substL_type]@nat_typechecks@lambda.intrs@bool_typechecks;
