(*  Title:      HOL/Sexp
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

S-expressions, general binary trees for defining recursive data structures
*)

open Sexp;

(** sexp_case **)

goalw Sexp.thy [sexp_case_def] "sexp_case c d e (Leaf a) = c(a)";
by (blast_tac (claset() addSIs [select_equality]) 1);
qed "sexp_case_Leaf";

goalw Sexp.thy [sexp_case_def] "sexp_case c d e (Numb k) = d(k)";
by (blast_tac (claset() addSIs [select_equality]) 1);
qed "sexp_case_Numb";

goalw Sexp.thy [sexp_case_def] "sexp_case c d e (M$N) = e M N";
by (blast_tac (claset() addSIs [select_equality]) 1);
qed "sexp_case_Scons";


(** Introduction rules for sexp constructors **)

val [prem] = goalw Sexp.thy [In0_def] "M: sexp ==> In0(M) : sexp";
by (rtac (prem RS (sexp.NumbI RS sexp.SconsI)) 1);
qed "sexp_In0I";

val [prem] = goalw Sexp.thy [In1_def] "M: sexp ==> In1(M) : sexp";
by (rtac (prem RS (sexp.NumbI RS sexp.SconsI)) 1);
qed "sexp_In1I";

AddIs (sexp.intrs@[SigmaI, uprodI]);

goal Sexp.thy "range(Leaf) <= sexp";
by (Blast_tac 1);
qed "range_Leaf_subset_sexp";

val [major] = goal Sexp.thy "M$N : sexp ==> M: sexp & N: sexp";
by (rtac (major RS setup_induction) 1);
by (etac sexp.induct 1);
by (ALLGOALS Blast_tac);
qed "Scons_D";

(** Introduction rules for 'pred_sexp' **)

goalw Sexp.thy [pred_sexp_def] "pred_sexp <= sexp Times sexp";
by (Blast_tac 1);
qed "pred_sexp_subset_Sigma";

(* (a,b) : pred_sexp^+ ==> a : sexp *)
val trancl_pred_sexpD1 = 
    pred_sexp_subset_Sigma RS trancl_subset_Sigma RS subsetD RS SigmaD1
and trancl_pred_sexpD2 = 
    pred_sexp_subset_Sigma RS trancl_subset_Sigma RS subsetD RS SigmaD2;

goalw Sexp.thy [pred_sexp_def]
    "!!M. [| M: sexp;  N: sexp |] ==> (M, M$N) : pred_sexp";
by (Blast_tac 1);
qed "pred_sexpI1";

goalw Sexp.thy [pred_sexp_def]
    "!!M. [| M: sexp;  N: sexp |] ==> (N, M$N) : pred_sexp";
by (Blast_tac 1);
qed "pred_sexpI2";

(*Combinations involving transitivity and the rules above*)
val pred_sexp_t1 = pred_sexpI1 RS r_into_trancl
and pred_sexp_t2 = pred_sexpI2 RS r_into_trancl;

val pred_sexp_trans1 = pred_sexp_t1 RSN (2, trans_trancl RS transD)
and pred_sexp_trans2 = pred_sexp_t2 RSN (2, trans_trancl RS transD);

(*Proves goals of the form (M,N):pred_sexp^+ provided M,N:sexp*)
Addsimps (sexp.intrs @ [pred_sexp_t1, pred_sexp_t2,
                        pred_sexp_trans1, pred_sexp_trans2, cut_apply]);

val major::prems = goalw Sexp.thy [pred_sexp_def]
    "[| p : pred_sexp;                                       \
\       !!M N. [| p = (M, M$N);  M: sexp;  N: sexp |] ==> R; \
\       !!M N. [| p = (N, M$N);  M: sexp;  N: sexp |] ==> R  \
\    |] ==> R";
by (cut_facts_tac [major] 1);
by (REPEAT (eresolve_tac ([asm_rl,emptyE,insertE,UN_E]@prems) 1));
qed "pred_sexpE";

goal Sexp.thy "wf(pred_sexp)";
by (rtac (pred_sexp_subset_Sigma RS wfI) 1);
by (etac sexp.induct 1);
by (ALLGOALS (blast_tac (claset() addSEs [allE, pred_sexpE])));
qed "wf_pred_sexp";


(*** sexp_rec -- by wf recursion on pred_sexp ***)

goal Sexp.thy
   "(%M. sexp_rec M c d e) = wfrec pred_sexp \
                       \ (%g. sexp_case c d (%N1 N2. e N1 N2 (g N1) (g N2)))";
by (simp_tac (HOL_ss addsimps [sexp_rec_def]) 1);
bind_thm("sexp_rec_unfold", 
	 [result() RS eq_reflection, wf_pred_sexp] MRS def_wfrec);

(** conversion rules **)

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
by (asm_simp_tac (simpset() addsimps [sexp_case_Scons,pred_sexpI1,pred_sexpI2])
    1);
qed "sexp_rec_Scons";
