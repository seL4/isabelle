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
by (asm_simp_tac lift_ss 1);
val unmark_Var = result();

goalw Terms.thy [unmark_def] 
    "unmark(Fun(t)) = Fun(unmark(t))";
by (asm_simp_tac lift_ss 1);
val unmark_Fun = result();

goalw Terms.thy [unmark_def] 
    "unmark(App(b,n,m)) = App(0,unmark(n),unmark(m))";
by (asm_simp_tac lift_ss 1);
val unmark_App = result();


(* ------------------------------------------------------------------------- *)
(*        term simplification set                                            *)
(* ------------------------------------------------------------------------- *)


val term_ss = res1_ss addsimps ([unmark_App,unmark_Fun,unmark_Var,
                                lambda.dom_subset RS subsetD]@lambda.intrs);


(* ------------------------------------------------------------------------- *)
(*        unmark lemmas                                                      *)
(* ------------------------------------------------------------------------- *)

goalw Terms.thy [unmark_def] 
    "!!u.u:redexes ==> unmark(u):lambda";
by (eresolve_tac [redexes.induct] 1);
by (ALLGOALS(asm_simp_tac term_ss));
val unmark_type = result();

goal Terms.thy  
    "!!u.u:lambda ==> unmark(u) = u";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS(asm_simp_tac term_ss));
val lambda_unmark = result();


(* ------------------------------------------------------------------------- *)
(*         lift and subst preserve lambda                                    *)
(* ------------------------------------------------------------------------- *)

goal Terms.thy  
    "!!u.[|v:lambda|]==> ALL k:nat.lift_rec(v,k):lambda";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS(asm_full_simp_tac (addsplit term_ss)));
val liftL_typea = result();
val liftL_type =liftL_typea RS bspec ;

goal Terms.thy  
    "!!n.[|v:lambda|]==>  ALL n:nat.ALL u:lambda.subst_rec(u,v,n):lambda";
by (eresolve_tac [lambda.induct] 1);
by (ALLGOALS(asm_full_simp_tac ((addsplit term_ss) addsimps [liftL_type])));
val substL_typea = result();
val substL_type = substL_typea RS bspec RS bspec ;


(* ------------------------------------------------------------------------- *)
(*        type-rule for reduction definitions                               *)
(* ------------------------------------------------------------------------- *)

val red_typechecks = [substL_type]@nat_typechecks@lambda.intrs@bool_typechecks;
