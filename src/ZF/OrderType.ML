(*  Title: 	ZF/OrderType.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

For OrderType.thy.  Order types in Zermelo-Fraenkel Set Theory 
*)


(*Requires Ordinal.thy as parent; otherwise could be in Order.ML*)
goal OrderType.thy "!!i. Ord(i) ==> well_ord(i, Memrel(i))";
by (rtac well_ordI 1);
by (rtac (wf_Memrel RS wf_imp_wf_on) 1);
by (asm_simp_tac (ZF_ss addsimps [linear_def, Memrel_iff]) 1);
by (REPEAT (resolve_tac [ballI, Ord_linear] 1));;
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));;
val well_ord_Memrel = result();

open OrderType;

goalw OrderType.thy [ordermap_def,ordertype_def]
    "ordermap(A,r) : A -> ordertype(A,r)";
by (rtac lam_type 1);
by (rtac (lamI RS imageI) 1);
by (REPEAT (assume_tac 1));
val ordermap_type = result();

(** Unfolding of ordermap **)

(*Useful for cardinality reasoning; see CardinalArith.ML*)
goalw OrderType.thy [ordermap_def, pred_def]
    "!!r. [| wf[A](r);  x:A |] ==> \
\         ordermap(A,r) ` x = ordermap(A,r) `` pred(A,x,r)";
by (asm_simp_tac ZF_ss 1);
by (etac (wfrec_on RS trans) 1);
by (assume_tac 1);
by (asm_simp_tac (ZF_ss addsimps [subset_iff, image_lam,
                                  vimage_singleton_iff]) 1);
val ordermap_eq_image = result();

goal OrderType.thy 
    "!!r. [| wf[A](r);  x:A |] ==> \
\         ordermap(A,r) ` x = {ordermap(A,r)`y . y : pred(A,x,r)}";
by (asm_simp_tac (ZF_ss addsimps [ordermap_eq_image, pred_subset, 
				  ordermap_type RS image_fun]) 1);
val ordermap_pred_unfold = result();

(*pred-unfolded version.  NOT suitable for rewriting -- loops!*)
val ordermap_unfold = rewrite_rule [pred_def] ordermap_pred_unfold;

(** Showing that ordermap, ordertype yield ordinals **)

fun ordermap_elim_tac i =
    EVERY [etac (ordermap_unfold RS equalityD1 RS subsetD RS RepFunE) i,
	   assume_tac (i+1),
	   assume_tac i];

goalw OrderType.thy [well_ord_def, tot_ord_def, part_ord_def]
    "!!r. [| well_ord(A,r);  x:A |] ==> Ord(ordermap(A,r) ` x)";
by (safe_tac ZF_cs);
by (wf_on_ind_tac "x" [] 1);
by (asm_simp_tac (ZF_ss addsimps [ordermap_pred_unfold]) 1);
by (rtac (Ord_is_Transset RSN (2,OrdI)) 1);
by (rewrite_goals_tac [pred_def,Transset_def]);
by (fast_tac ZF_cs 2);
by (safe_tac ZF_cs);
by (ordermap_elim_tac 1);
by (fast_tac (ZF_cs addSEs [trans_onD]) 1);
val Ord_ordermap = result();

goalw OrderType.thy [ordertype_def]
    "!!r. well_ord(A,r) ==> Ord(ordertype(A,r))";
by (rtac ([ordermap_type, subset_refl] MRS image_fun RS ssubst) 1);
by (rtac (Ord_is_Transset RSN (2,OrdI)) 1);
by (fast_tac (ZF_cs addIs [Ord_ordermap]) 2);
by (rewrite_goals_tac [Transset_def,well_ord_def]);
by (safe_tac ZF_cs);
by (ordermap_elim_tac 1);
by (fast_tac ZF_cs 1);
val Ord_ordertype = result();

(** ordermap preserves the orderings in both directions **)

goal OrderType.thy
    "!!r. [| <w,x>: r;  wf[A](r);  w: A; x: A |] ==>	\
\         ordermap(A,r)`w : ordermap(A,r)`x";
by (eres_inst_tac [("x1", "x")] (ordermap_unfold RS ssubst) 1);
by (assume_tac 1);
by (fast_tac ZF_cs 1);
val less_imp_ordermap_in = result();

(*linearity of r is crucial here*)
goalw OrderType.thy [well_ord_def, tot_ord_def]
    "!!r. [| ordermap(A,r)`w : ordermap(A,r)`x;  well_ord(A,r);  \
\            w: A; x: A |] ==> <w,x>: r";
by (safe_tac ZF_cs);
by (linear_case_tac 1);
by (fast_tac (ZF_cs addSEs [mem_not_refl RS notE]) 1);
by (dtac less_imp_ordermap_in 1);
by (REPEAT_SOME assume_tac);
by (etac mem_asym 1);
by (assume_tac 1);
val ordermap_in_imp_less = result();

val ordermap_surj = 
    (ordermap_type RS surj_image) |>
    rewrite_rule [symmetric ordertype_def] |> 
    standard;

goalw OrderType.thy [well_ord_def, tot_ord_def, bij_def, inj_def]
    "!!r. well_ord(A,r) ==> ordermap(A,r) : bij(A, ordertype(A,r))";
by (safe_tac ZF_cs);
by (rtac ordermap_type 1);
by (rtac ordermap_surj 2);
by (linear_case_tac 1);
(*The two cases yield similar contradictions*)
by (ALLGOALS (dtac less_imp_ordermap_in));
by (REPEAT_SOME assume_tac);
by (ALLGOALS (asm_full_simp_tac (ZF_ss addsimps [mem_not_refl])));
val ordertype_bij = result();

goalw OrderType.thy [ord_iso_def]
 "!!r. well_ord(A,r) ==> \
\      ordermap(A,r) : ord_iso(A,r, ordertype(A,r), Memrel(ordertype(A,r)))";
by (safe_tac ZF_cs);
by (rtac ordertype_bij 1);
by (assume_tac 1);
by (fast_tac (ZF_cs addSEs [MemrelE, ordermap_in_imp_less]) 2);
by (rewtac well_ord_def);
by (fast_tac (ZF_cs addSIs [MemrelI, less_imp_ordermap_in,
			    ordermap_type RS apply_type]) 1);
val ordertype_ord_iso = result();


(** Unfolding of ordertype **)

goalw OrderType.thy [ordertype_def]
    "ordertype(A,r) = {ordermap(A,r)`y . y : A}";
by (rtac ([ordermap_type, subset_refl] MRS image_fun) 1);
val ordertype_unfold = result();
