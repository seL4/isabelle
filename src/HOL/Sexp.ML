(*  Title: 	HOL/Sexp
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

S-expressions, general binary trees for defining recursive data structures
*)

open Sexp;

(** sexp_case **)

val sexp_free_cs = 
    set_cs addSDs [Leaf_inject, Numb_inject, Scons_inject] 
	   addSEs [Leaf_neq_Scons, Leaf_neq_Numb,
		   Numb_neq_Scons, Numb_neq_Leaf,
		   Scons_neq_Leaf, Scons_neq_Numb];

goalw Sexp.thy [sexp_case_def] "sexp_case c d e (Leaf a) = c(a)";
by (resolve_tac [select_equality] 1);
by (ALLGOALS (fast_tac sexp_free_cs));
qed "sexp_case_Leaf";

goalw Sexp.thy [sexp_case_def] "sexp_case c d e (Numb k) = d(k)";
by (resolve_tac [select_equality] 1);
by (ALLGOALS (fast_tac sexp_free_cs));
qed "sexp_case_Numb";

goalw Sexp.thy [sexp_case_def] "sexp_case c d e (M$N) = e M N";
by (resolve_tac [select_equality] 1);
by (ALLGOALS (fast_tac sexp_free_cs));
qed "sexp_case_Scons";


(** Introduction rules for sexp constructors **)

val [prem] = goalw Sexp.thy [In0_def] 
    "M: sexp ==> In0(M) : sexp";
by (rtac (prem RS (sexp.NumbI RS sexp.SconsI)) 1);
qed "sexp_In0I";

val [prem] = goalw Sexp.thy [In1_def] 
    "M: sexp ==> In1(M) : sexp";
by (rtac (prem RS (sexp.NumbI RS sexp.SconsI)) 1);
qed "sexp_In1I";

val sexp_cs = set_cs addIs sexp.intrs@[SigmaI, uprodI];

goal Sexp.thy "range(Leaf) <= sexp";
by (fast_tac sexp_cs 1);
qed "range_Leaf_subset_sexp";

val [major] = goal Sexp.thy "M$N : sexp ==> M: sexp & N: sexp";
by (rtac (major RS setup_induction) 1);
by (etac sexp.induct 1);
by (ALLGOALS 
    (fast_tac (set_cs addSEs [Scons_neq_Leaf,Scons_neq_Numb,Scons_inject])));
qed "Scons_D";

(** Introduction rules for 'pred_sexp' **)

goalw Sexp.thy [pred_sexp_def] "pred_sexp <= Sigma sexp (%u.sexp)";
by (fast_tac sexp_cs 1);
qed "pred_sexp_subset_Sigma";

(* <a,b> : pred_sexp^+ ==> a : sexp *)
val trancl_pred_sexpD1 = 
    pred_sexp_subset_Sigma RS trancl_subset_Sigma RS subsetD RS SigmaD1
and trancl_pred_sexpD2 = 
    pred_sexp_subset_Sigma RS trancl_subset_Sigma RS subsetD RS SigmaD2;

val prems = goalw Sexp.thy [pred_sexp_def]
    "[| M: sexp;  N: sexp |] ==> <M, M$N> : pred_sexp";
by (fast_tac (set_cs addIs prems) 1);
qed "pred_sexpI1";

val prems = goalw Sexp.thy [pred_sexp_def]
    "[| M: sexp;  N: sexp |] ==> <N, M$N> : pred_sexp";
by (fast_tac (set_cs addIs prems) 1);
qed "pred_sexpI2";

(*Combinations involving transitivity and the rules above*)
val pred_sexp_t1 = pred_sexpI1 RS r_into_trancl
and pred_sexp_t2 = pred_sexpI2 RS r_into_trancl;

val pred_sexp_trans1 = pred_sexp_t1 RSN (2, trans_trancl RS transD)
and pred_sexp_trans2 = pred_sexp_t2 RSN (2, trans_trancl RS transD);

(*Proves goals of the form <M,N>:pred_sexp^+ provided M,N:sexp*)
val pred_sexp_simps =
            sexp.intrs @
	    [pred_sexp_t1, pred_sexp_t2,
	     pred_sexp_trans1, pred_sexp_trans2, cut_apply];
val pred_sexp_ss = HOL_ss addsimps pred_sexp_simps;

val major::prems = goalw Sexp.thy [pred_sexp_def]
    "[| p : pred_sexp;  \
\       !!M N. [| p = <M, M$N>;  M: sexp;  N: sexp |] ==> R; \
\       !!M N. [| p = <N, M$N>;  M: sexp;  N: sexp |] ==> R  \
\    |] ==> R";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac ([asm_rl,emptyE,insertE,UN_E]@prems) 1));
qed "pred_sexpE";

goal Sexp.thy "wf(pred_sexp)";
by (rtac (pred_sexp_subset_Sigma RS wfI) 1);
by (etac sexp.induct 1);
by (fast_tac (HOL_cs addSEs [mp, pred_sexpE, Pair_inject, Scons_inject]) 3);
by (fast_tac (HOL_cs addSEs [mp, pred_sexpE, Pair_inject, Numb_neq_Scons]) 2);
by (fast_tac (HOL_cs addSEs [mp, pred_sexpE, Pair_inject, Leaf_neq_Scons]) 1);
qed "wf_pred_sexp";

(*** sexp_rec -- by wf recursion on pred_sexp ***)

(** conversion rules **)

val sexp_rec_unfold = wf_pred_sexp RS (sexp_rec_def RS def_wfrec);


goal Sexp.thy "sexp_rec (Leaf a) c d h = c(a)";
by (stac sexp_rec_unfold 1);
by (rtac sexp_case_Leaf 1);
qed "sexp_rec_Leaf";

goal Sexp.thy "sexp_rec (Numb k) c d h = d(k)";
by (stac sexp_rec_unfold 1);
by (rtac sexp_case_Numb 1);
qed "sexp_rec_Numb";

goal Sexp.thy "!!M. [| M: sexp;  N: sexp |] ==> \
\    sexp_rec (M$N) c d h = h M N (sexp_rec M c d h) (sexp_rec N c d h)";
by (rtac (sexp_rec_unfold RS trans) 1);
by (asm_simp_tac(HOL_ss addsimps
               [sexp_case_Scons,pred_sexpI1,pred_sexpI2,cut_apply])1);
qed "sexp_rec_Scons";
