(*  Title:      Terms.ML
    ID:         $Id$
    Author:     Ole Rasmussen
    Copyright   1995  University of Cambridge
    Logic Image: ZF
*)

open Terms;

(* ------------------------------------------------------------------------- *)
(*       unmark simplifications                                              *)
(* ------------------------------------------------------------------------- *)

Goalw [unmark_def] "unmark(Var(n)) = Var(n)";
by (Asm_simp_tac 1);
qed "unmark_Var";

Goalw [unmark_def] "unmark(Fun(t)) = Fun(unmark(t))";
by (Asm_simp_tac 1);
qed "unmark_Fun";

Goalw [unmark_def] "unmark(App(b,n,m)) = App(0,unmark(n),unmark(m))";
by (Asm_simp_tac 1);
qed "unmark_App";


(* ------------------------------------------------------------------------- *)
(*        term simplification set                                            *)
(* ------------------------------------------------------------------------- *)


Addsimps ([unmark_App, unmark_Fun, unmark_Var,
	   lambda.dom_subset RS subsetD] @ 
	  lambda.intrs);


(* ------------------------------------------------------------------------- *)
(*        unmark lemmas                                                      *)
(* ------------------------------------------------------------------------- *)

Goalw [unmark_def] 
    "u:redexes ==> unmark(u):lambda";
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
qed "liftL_typea";
val liftL_type =liftL_typea RS bspec ;

Goal "v:lambda ==>  ALL n:nat. ALL u:lambda. subst_rec(u,v,n):lambda";
by (etac lambda.induct 1);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [liftL_type,subst_Var])));
qed "substL_typea";
val substL_type = substL_typea RS bspec RS bspec ;


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

val red_typechecks = [substL_type]@nat_typechecks@lambda.intrs@bool_typechecks;
