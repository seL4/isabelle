(*  Title: 	ZF/OrderType.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

For OrderType.thy.  Order types in Zermelo-Fraenkel Set Theory 
*)


open OrderType;

goalw OrderType.thy [ordermap_def,ordertype_def]
    "ordermap(A,r) : A -> ordertype(A,r)";
by (rtac lam_type 1);
by (rtac (lamI RS imageI) 1);
by (REPEAT (assume_tac 1));
qed "ordermap_type";

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
qed "ordermap_eq_image";

(*Useful for rewriting PROVIDED pred is not unfolded until later!*)
goal OrderType.thy 
    "!!r. [| wf[A](r);  x:A |] ==> \
\         ordermap(A,r) ` x = {ordermap(A,r)`y . y : pred(A,x,r)}";
by (asm_simp_tac (ZF_ss addsimps [ordermap_eq_image, pred_subset, 
				  ordermap_type RS image_fun]) 1);
qed "ordermap_pred_unfold";

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
qed "Ord_ordermap";

goalw OrderType.thy [ordertype_def]
    "!!r. well_ord(A,r) ==> Ord(ordertype(A,r))";
by (rtac ([ordermap_type, subset_refl] MRS image_fun RS ssubst) 1);
by (rtac (Ord_is_Transset RSN (2,OrdI)) 1);
by (fast_tac (ZF_cs addIs [Ord_ordermap]) 2);
by (rewrite_goals_tac [Transset_def,well_ord_def]);
by (safe_tac ZF_cs);
by (ordermap_elim_tac 1);
by (fast_tac ZF_cs 1);
qed "Ord_ordertype";

(** ordermap preserves the orderings in both directions **)

goal OrderType.thy
    "!!r. [| <w,x>: r;  wf[A](r);  w: A; x: A |] ==>	\
\         ordermap(A,r)`w : ordermap(A,r)`x";
by (eres_inst_tac [("x1", "x")] (ordermap_unfold RS ssubst) 1);
by (assume_tac 1);
by (fast_tac ZF_cs 1);
qed "ordermap_mono";

(*linearity of r is crucial here*)
goalw OrderType.thy [well_ord_def, tot_ord_def]
    "!!r. [| ordermap(A,r)`w : ordermap(A,r)`x;  well_ord(A,r);  \
\            w: A; x: A |] ==> <w,x>: r";
by (safe_tac ZF_cs);
by (linear_case_tac 1);
by (fast_tac (ZF_cs addSEs [mem_not_refl RS notE]) 1);
by (dtac ordermap_mono 1);
by (REPEAT_SOME assume_tac);
by (etac mem_asym 1);
by (assume_tac 1);
qed "converse_ordermap_mono";

bind_thm ("ordermap_surj", 
	  rewrite_rule [symmetric ordertype_def] 
	      (ordermap_type RS surj_image));

goalw OrderType.thy [well_ord_def, tot_ord_def, bij_def, inj_def]
    "!!r. well_ord(A,r) ==> ordermap(A,r) : bij(A, ordertype(A,r))";
by (safe_tac ZF_cs);
by (rtac ordermap_type 1);
by (rtac ordermap_surj 2);
by (linear_case_tac 1);
(*The two cases yield similar contradictions*)
by (ALLGOALS (dtac ordermap_mono));
by (REPEAT_SOME assume_tac);
by (ALLGOALS (asm_full_simp_tac (ZF_ss addsimps [mem_not_refl])));
qed "ordermap_bij";

goalw OrderType.thy [ord_iso_def]
 "!!r. well_ord(A,r) ==> \
\      ordermap(A,r) : ord_iso(A,r, ordertype(A,r), Memrel(ordertype(A,r)))";
by (safe_tac ZF_cs);
by (rtac ordermap_bij 1);
by (assume_tac 1);
by (fast_tac (ZF_cs addSEs [MemrelE, converse_ordermap_mono]) 2);
by (rewtac well_ord_def);
by (fast_tac (ZF_cs addSIs [MemrelI, ordermap_mono,
			    ordermap_type RS apply_type]) 1);
qed "ordertype_ord_iso";


(** Unfolding of ordertype **)

goalw OrderType.thy [ordertype_def]
    "ordertype(A,r) = {ordermap(A,r)`y . y : A}";
by (rtac ([ordermap_type, subset_refl] MRS image_fun) 1);
qed "ordertype_unfold";


(** Ordertype of Memrel **)

(*Requires Ordinal.thy as parent; otherwise could be in Order.ML*)
goal OrderType.thy "!!i. Ord(i) ==> well_ord(i, Memrel(i))";
by (rtac well_ordI 1);
by (rtac (wf_Memrel RS wf_imp_wf_on) 1);
by (asm_simp_tac (ZF_ss addsimps [linear_def, Memrel_iff]) 1);
by (REPEAT (resolve_tac [ballI, Ord_linear] 1));;
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));;
qed "well_ord_Memrel";

goal OrderType.thy "!!i. [| Ord(i);  j:i |] ==> ordermap(i,Memrel(i)) ` j = j";
by (etac Ord_induct 1);
by (assume_tac 1);
by (asm_simp_tac (ZF_ss addsimps
	     [well_ord_Memrel RS well_ord_is_wf RS ordermap_pred_unfold]) 1);
by (asm_simp_tac (ZF_ss addsimps [pred_def, Memrel_iff]) 1);
by (dtac OrdmemD 1);
by (assume_tac 1);
by (fast_tac eq_cs 1);
qed "ordermap_Memrel";

goal OrderType.thy "!!i. Ord(i) ==> ordertype(i,Memrel(i)) = i";
by (asm_simp_tac (ZF_ss addsimps [ordertype_unfold, ordermap_Memrel]) 1);
qed "ordertype_Memrel";

(** Ordertype of rvimage **)

goal OrderType.thy
    "!!f. [| f: bij(A,B);  well_ord(B,r);  x:A |] ==>	\
\         ordermap(A,rvimage(A,f,r)) ` x = ordermap(B,r) ` (f`x)";
by (metacut_tac well_ord_rvimage 1 THEN 
    etac bij_is_inj 2 THEN assume_tac 2);
by (res_inst_tac [("A","A"), ("a","x")] wf_on_induct 1 THEN
    REPEAT (ares_tac [well_ord_is_wf] 1));
by (asm_simp_tac
    (bij_inverse_ss addsimps [ordermap_pred_unfold, well_ord_is_wf]) 1);
by (asm_simp_tac (ZF_ss addsimps [pred_def, rvimage_iff]) 1);
by (safe_tac eq_cs);
by (fast_tac bij_apply_cs 1);
by (res_inst_tac [("a", "converse(f)`xb")] RepFun_eqI 1);
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
qed "bij_ordermap_vimage";

goal OrderType.thy
    "!!f. [| f: bij(A,B);  well_ord(B,r) |] ==>	\
\    ordertype(A,rvimage(A,f,r)) = ordertype(B,r)";
by (asm_simp_tac (ZF_ss addsimps [ordertype_unfold, bij_ordermap_vimage]) 1);
by (safe_tac eq_cs);
by (fast_tac bij_apply_cs 1);
by (res_inst_tac [("a", "converse(f)`xa")] RepFun_eqI 1);
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
qed "bij_ordertype_vimage";


goal OrderType.thy
    "!!r. [| well_ord(A,r);  y:A;  z: pred(A,y,r) |] ==>	\
\	  ordermap(pred(A,y,r), r) ` z = ordermap(A, r) ` z";
by (forward_tac [[well_ord_is_wf, pred_subset] MRS wf_on_subset_A] 1);
by (wf_on_ind_tac "z" [] 1);
by (safe_tac (ZF_cs addSEs [predE]));
by (asm_simp_tac
    (ZF_ss addsimps [ordermap_pred_unfold, well_ord_is_wf, pred_iff]) 1);
(*combining these two simplifications LOOPS! *)
by (asm_simp_tac (ZF_ss addsimps [pred_pred_eq]) 1);
by (asm_full_simp_tac (ZF_ss addsimps [pred_def]) 1);
by (rtac (refl RSN (2,RepFun_cong)) 1);
by (dtac well_ord_is_trans_on 1);
by (fast_tac (eq_cs addSEs [trans_onD]) 1);
qed "ordermap_pred_eq_ordermap";


goal OrderType.thy
    "!!r. [| well_ord(A,r);  i: ordertype(A,r) |] ==>	\
\	  EX B. B<=A & i = ordertype(B,r)";
by (dresolve_tac [ordertype_unfold RS equalityD1 RS subsetD] 1);
by (res_inst_tac [("x", "pred(A, converse(ordermap(A,r))`i, r)")]  exI  1);
by (safe_tac (ZF_cs addSEs [predE]));
by (asm_simp_tac (ZF_ss addsimps [ordermap_bij RS left_inverse_bij]) 1);
by (asm_simp_tac (ZF_ss addsimps
		  [well_ord_is_wf RS ordermap_pred_unfold]) 1);
by (asm_simp_tac (ZF_ss addsimps [ordertype_unfold,
				  ordermap_pred_eq_ordermap]) 1);
qed "ordertype_subset";


(*Kunen's Theorem 7.3 (i), page 16;  see also Ordinal/Ord_in_Ord
  The smaller ordinal is an initial segment of the larger *)
goalw OrderType.thy [pred_def, lt_def]
    "!!i j. j<i ==> j = pred(i, j, Memrel(i))";
by (asm_simp_tac (ZF_ss addsimps [Memrel_iff]) 1);
by (fast_tac (eq_cs addEs [Ord_trans]) 1);
qed "lt_eq_pred";

goal OrderType.thy
    "!!i. [| j<i;  f: ord_iso(i,Memrel(i),j,Memrel(j))	\
\         |] ==> R";
by (forward_tac [lt_eq_pred] 1);
by (etac ltE 1);
by (rtac (well_ord_Memrel RS well_ord_iso_predE) 1 THEN
    assume_tac 3 THEN assume_tac 1);
by (etac subst 1);
by (asm_full_simp_tac (ZF_ss addsimps [ord_iso_def]) 1);
(*Combining the two simplifications causes looping*)
by (asm_simp_tac (ZF_ss addsimps [Memrel_iff]) 1);
by (fast_tac (ZF_cs addSEs [bij_is_fun RS apply_type]  
                    addEs  [Ord_trans]) 1);
qed "Ord_iso_implies_eq_lemma";

(*Kunen's Theorem 7.3 (ii), page 16.  Isomorphic ordinals are equal*)
goal OrderType.thy
    "!!i. [| Ord(i);  Ord(j);  f:  ord_iso(i,Memrel(i),j,Memrel(j))	\
\         |] ==> i=j";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_lt 1);
by (REPEAT (eresolve_tac [asm_rl, ord_iso_sym, Ord_iso_implies_eq_lemma] 1));
qed "Ord_iso_implies_eq";
