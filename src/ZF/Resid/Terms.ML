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

goalw Terms.thy [unmark_def] 
    "unmark(Var(n)) = Var(n)";
by (Asm_simp_tac 1);
qed "unmark_Var";

goalw Terms.thy [unmark_def] 
    "unmark(Fun(t)) = Fun(unmark(t))";
by (Asm_simp_tac 1);
qed "unmark_Fun";

goalw Terms.thy [unmark_def] 
    "unmark(App(b,n,m)) = App(0,unmark(n),unmark(m))";
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

goalw Terms.thy [unmark_def] 
    "!!u. u:redexes ==> unmark(u):lambda";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS Asm_simp_tac);
qed "unmark_type";

goal Terms.thy  
    "!!u. u:lambda ==> unmark(u) = u";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS Asm_simp_tac);
qed "lambda_unmark";


(* ------------------------------------------------------------------------- *)
(*         lift and subst preserve lambda                                    *)
(* ------------------------------------------------------------------------- *)

goal Terms.thy  
    "!!u.[|v:lambda|]==> ALL k:nat. lift_rec(v,k):lambda";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS(asm_full_simp_tac (addsplit (!simpset))));
qed "liftL_typea";
val liftL_type =liftL_typea RS bspec ;

goal Terms.thy  
    "!!n.[|v:lambda|]==>  ALL n:nat. ALL u:lambda. subst_rec(u,v,n):lambda";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS(asm_full_simp_tac ((addsplit (!simpset)) addsimps [liftL_type])));
qed "substL_typea";
val substL_type = substL_typea RS bspec RS bspec ;


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

val red_typechecks = [substL_type]@nat_typechecks@lambda.intrs@bool_typechecks;
