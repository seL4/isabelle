(*  Title:      ZF/OrderType.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Order types and ordinal arithmetic in Zermelo-Fraenkel Set Theory 

Ordinal arithmetic is traditionally defined in terms of order types, as here.
But a definition by transfinite recursion would be much simpler!
*)


open OrderType;

(**** Proofs needing the combination of Ordinal.thy and Order.thy ****)

val [prem] = goal OrderType.thy "j le i ==> well_ord(j, Memrel(i))";
by (rtac well_ordI 1);
by (rtac (wf_Memrel RS wf_imp_wf_on) 1);
by (resolve_tac [prem RS ltE] 1);
by (asm_simp_tac (ZF_ss addsimps [linear_def, Memrel_iff,
                                  [ltI, prem] MRS lt_trans2 RS ltD]) 1);
by (REPEAT (resolve_tac [ballI, Ord_linear] 1));
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));
qed "le_well_ord_Memrel";

(*"Ord(i) ==> well_ord(i, Memrel(i))"*)
bind_thm ("well_ord_Memrel", le_refl RS le_well_ord_Memrel);

(*Kunen's Theorem 7.3 (i), page 16;  see also Ordinal/Ord_in_Ord
  The smaller ordinal is an initial segment of the larger *)
goalw OrderType.thy [pred_def, lt_def]
    "!!i j. j<i ==> pred(i, j, Memrel(i)) = j";
by (asm_simp_tac (ZF_ss addsimps [Memrel_iff]) 1);
by (fast_tac (eq_cs addEs [Ord_trans]) 1);
qed "lt_pred_Memrel";

goalw OrderType.thy [pred_def,Memrel_def] 
      "!!A x. x:A ==> pred(A, x, Memrel(A)) = A Int x";
by (fast_tac eq_cs 1);
qed "pred_Memrel";

goal OrderType.thy
    "!!i. [| j<i;  f: ord_iso(i,Memrel(i),j,Memrel(j)) |] ==> R";
by (forward_tac [lt_pred_Memrel] 1);
by (etac ltE 1);
by (rtac (well_ord_Memrel RS well_ord_iso_predE) 1 THEN
    assume_tac 3 THEN assume_tac 1);
by (asm_full_simp_tac (ZF_ss addsimps [ord_iso_def]) 1);
(*Combining the two simplifications causes looping*)
by (asm_simp_tac (ZF_ss addsimps [Memrel_iff]) 1);
by (fast_tac (ZF_cs addSEs [bij_is_fun RS apply_type] addEs [Ord_trans]) 1);
qed "Ord_iso_implies_eq_lemma";

(*Kunen's Theorem 7.3 (ii), page 16.  Isomorphic ordinals are equal*)
goal OrderType.thy
    "!!i. [| Ord(i);  Ord(j);  f:  ord_iso(i,Memrel(i),j,Memrel(j))     \
\         |] ==> i=j";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_lt 1);
by (REPEAT (eresolve_tac [asm_rl, ord_iso_sym, Ord_iso_implies_eq_lemma] 1));
qed "Ord_iso_implies_eq";


(**** Ordermap and ordertype ****)

goalw OrderType.thy [ordermap_def,ordertype_def]
    "ordermap(A,r) : A -> ordertype(A,r)";
by (rtac lam_type 1);
by (rtac (lamI RS imageI) 1);
by (REPEAT (assume_tac 1));
qed "ordermap_type";

(*** Unfolding of ordermap ***)

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

(*** Showing that ordermap, ordertype yield ordinals ***)

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

(*** ordermap preserves the orderings in both directions ***)

goal OrderType.thy
    "!!r. [| <w,x>: r;  wf[A](r);  w: A; x: A |] ==>    \
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
by (fast_tac (ZF_cs addSIs [ordermap_type, ordermap_surj]
                    addEs [linearE]
                    addDs [ordermap_mono]
                    addss (ZF_ss addsimps [mem_not_refl])) 1);
qed "ordermap_bij";

(*** Isomorphisms involving ordertype ***)

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

goal OrderType.thy
    "!!f. [| f: ord_iso(A,r,B,s);  well_ord(B,s) |] ==> \
\    ordertype(A,r) = ordertype(B,s)";
by (forward_tac [well_ord_ord_iso] 1 THEN assume_tac 1);
by (rtac Ord_iso_implies_eq 1
    THEN REPEAT (etac Ord_ordertype 1));
by (deepen_tac (ZF_cs addIs  [ord_iso_trans, ord_iso_sym]
                      addSEs [ordertype_ord_iso]) 0 1);
qed "ordertype_eq";

goal OrderType.thy
    "!!A B. [| ordertype(A,r) = ordertype(B,s); \
\              well_ord(A,r);  well_ord(B,s) \
\           |] ==> EX f. f: ord_iso(A,r,B,s)";
by (rtac exI 1);
by (resolve_tac [ordertype_ord_iso RS ord_iso_trans] 1);
by (assume_tac 1);
by (etac ssubst 1);
by (eresolve_tac [ordertype_ord_iso RS ord_iso_sym] 1);
qed "ordertype_eq_imp_ord_iso";

(*** Basic equalities for ordertype ***)

(*Ordertype of Memrel*)
goal OrderType.thy "!!i. j le i ==> ordertype(j,Memrel(i)) = j";
by (resolve_tac [Ord_iso_implies_eq RS sym] 1);
by (etac ltE 1);
by (REPEAT (ares_tac [le_well_ord_Memrel, Ord_ordertype] 1));
by (rtac ord_iso_trans 1);
by (eresolve_tac [le_well_ord_Memrel RS ordertype_ord_iso] 2);
by (resolve_tac [id_bij RS ord_isoI] 1);
by (asm_simp_tac (ZF_ss addsimps [id_conv, Memrel_iff]) 1);
by (fast_tac (ZF_cs addEs [ltE, Ord_in_Ord, Ord_trans]) 1);
qed "le_ordertype_Memrel";

(*"Ord(i) ==> ordertype(i, Memrel(i)) = i"*)
bind_thm ("ordertype_Memrel", le_refl RS le_ordertype_Memrel);

goal OrderType.thy "ordertype(0,r) = 0";
by (resolve_tac [id_bij RS ord_isoI RS ordertype_eq RS trans] 1);
by (etac emptyE 1);
by (rtac well_ord_0 1);
by (resolve_tac [Ord_0 RS ordertype_Memrel] 1);
qed "ordertype_0";

(*Ordertype of rvimage:  [| f: bij(A,B);  well_ord(B,s) |] ==>
                         ordertype(A, rvimage(A,f,s)) = ordertype(B,s) *)
bind_thm ("bij_ordertype_vimage", ord_iso_rvimage RS ordertype_eq);

(*** A fundamental unfolding law for ordertype. ***)

(*Ordermap returns the same result if applied to an initial segment*)
goal OrderType.thy
    "!!r. [| well_ord(A,r);  y:A;  z: pred(A,y,r) |] ==>        \
\         ordermap(pred(A,y,r), r) ` z = ordermap(A, r) ` z";
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

goalw OrderType.thy [ordertype_def]
    "ordertype(A,r) = {ordermap(A,r)`y . y : A}";
by (rtac ([ordermap_type, subset_refl] MRS image_fun) 1);
qed "ordertype_unfold";

(** Theorems by Krzysztof Grabczewski; proofs simplified by lcp **)

goal OrderType.thy
    "!!r. [| well_ord(A,r);  x:A |] ==>  \
\         ordertype(pred(A,x,r),r) <= ordertype(A,r)";
by (asm_simp_tac (ZF_ss addsimps [ordertype_unfold, 
                  pred_subset RSN (2, well_ord_subset)]) 1);
by (fast_tac (ZF_cs addIs [ordermap_pred_eq_ordermap, RepFun_eqI]
                    addEs [predE]) 1);
qed "ordertype_pred_subset";

goal OrderType.thy
    "!!r. [| well_ord(A,r);  x:A |] ==>  \
\         ordertype(pred(A,x,r),r) < ordertype(A,r)";
by (resolve_tac [ordertype_pred_subset RS subset_imp_le RS leE] 1);
by (REPEAT (ares_tac [Ord_ordertype, well_ord_subset, pred_subset] 1));
by (eresolve_tac [sym RS ordertype_eq_imp_ord_iso RS exE] 1);
by (etac well_ord_iso_predE 3);
by (REPEAT (ares_tac [pred_subset, well_ord_subset] 1));
qed "ordertype_pred_lt";

(*May rewrite with this -- provided no rules are supplied for proving that
        well_ord(pred(A,x,r), r) *)
goal OrderType.thy
    "!!A r. well_ord(A,r) ==>  \
\           ordertype(A,r) = {ordertype(pred(A,x,r),r). x:A}";
by (safe_tac (eq_cs addSIs [ordertype_pred_lt RS ltD]));
by (fast_tac
    (ZF_cs addss
     (ZF_ss addsimps [ordertype_def, 
                      well_ord_is_wf RS ordermap_eq_image, 
                      ordermap_type RS image_fun, 
                      ordermap_pred_eq_ordermap, 
                      pred_subset]))
    1);
qed "ordertype_pred_unfold";


(**** Alternative definition of ordinal ****)

(*proof by Krzysztof Grabczewski*)
goalw OrderType.thy [Ord_alt_def] "!!i. Ord(i) ==> Ord_alt(i)";
by (rtac conjI 1);
by (etac well_ord_Memrel 1);
by (rewrite_goals_tac [Ord_def, Transset_def, pred_def, Memrel_def]);
by (fast_tac eq_cs 1);
qed "Ord_is_Ord_alt";

(*proof by lcp*)
goalw OrderType.thy [Ord_alt_def, Ord_def, Transset_def, well_ord_def, 
                     tot_ord_def, part_ord_def, trans_on_def] 
    "!!i. Ord_alt(i) ==> Ord(i)";
by (asm_full_simp_tac (ZF_ss addsimps [Memrel_iff, pred_Memrel]) 1);
by (safe_tac ZF_cs);
by (fast_tac (ZF_cs addSDs [equalityD1]) 1);
by (subgoal_tac "xa: i" 1);
by (fast_tac (ZF_cs addSDs [equalityD1]) 2);
by (fast_tac (ZF_cs addSDs [equalityD1]
                    addSEs [bspec RS bspec RS bspec RS mp RS mp]) 1);
qed "Ord_alt_is_Ord";


(**** Ordinal Addition ****)

(*** Order Type calculations for radd ***)

(** Addition with 0 **)

goal OrderType.thy "(lam z:A+0. case(%x.x, %y.y, z)) : bij(A+0, A)";
by (res_inst_tac [("d", "Inl")] lam_bijective 1);
by (safe_tac sum_cs);
by (ALLGOALS (asm_simp_tac sum_ss));
qed "bij_sum_0";

goal OrderType.thy
 "!!A r. well_ord(A,r) ==> ordertype(A+0, radd(A,r,0,s)) = ordertype(A,r)";
by (resolve_tac [bij_sum_0 RS ord_isoI RS ordertype_eq] 1);
by (assume_tac 2);
by (fast_tac (sum_cs addss (sum_ss addsimps [radd_Inl_iff, Memrel_iff])) 1);
qed "ordertype_sum_0_eq";

goal OrderType.thy "(lam z:0+A. case(%x.x, %y.y, z)) : bij(0+A, A)";
by (res_inst_tac [("d", "Inr")] lam_bijective 1);
by (safe_tac sum_cs);
by (ALLGOALS (asm_simp_tac sum_ss));
qed "bij_0_sum";

goal OrderType.thy
 "!!A r. well_ord(A,r) ==> ordertype(0+A, radd(0,s,A,r)) = ordertype(A,r)";
by (resolve_tac [bij_0_sum RS ord_isoI RS ordertype_eq] 1);
by (assume_tac 2);
by (fast_tac (sum_cs addss (sum_ss addsimps [radd_Inr_iff, Memrel_iff])) 1);
qed "ordertype_0_sum_eq";

(** Initial segments of radd.  Statements by Grabczewski **)

(*In fact, pred(A+B, Inl(a), radd(A,r,B,s)) = pred(A,a,r)+0 *)
goalw OrderType.thy [pred_def]
 "!!A B. a:A ==>  \
\        (lam x:pred(A,a,r). Inl(x))    \
\        : bij(pred(A,a,r), pred(A+B, Inl(a), radd(A,r,B,s)))";
by (res_inst_tac [("d", "case(%x.x, %y.y)")] lam_bijective 1);
by (safe_tac sum_cs);
by (ALLGOALS
    (asm_full_simp_tac 
     (sum_ss addsimps [radd_Inl_iff, radd_Inr_Inl_iff])));
qed "pred_Inl_bij";

goal OrderType.thy
 "!!A B. [| a:A;  well_ord(A,r) |] ==>  \
\        ordertype(pred(A+B, Inl(a), radd(A,r,B,s)), radd(A,r,B,s)) = \
\        ordertype(pred(A,a,r), r)";
by (resolve_tac [pred_Inl_bij RS ord_isoI RS ord_iso_sym RS ordertype_eq] 1);
by (REPEAT_FIRST (ares_tac [pred_subset, well_ord_subset]));
by (asm_full_simp_tac (ZF_ss addsimps [radd_Inl_iff, pred_def]) 1);
qed "ordertype_pred_Inl_eq";

goalw OrderType.thy [pred_def, id_def]
 "!!A B. b:B ==>  \
\        id(A+pred(B,b,s))      \
\        : bij(A+pred(B,b,s), pred(A+B, Inr(b), radd(A,r,B,s)))";
by (res_inst_tac [("d", "%z.z")] lam_bijective 1);
by (safe_tac sum_cs);
by (ALLGOALS (asm_full_simp_tac radd_ss));
qed "pred_Inr_bij";

goal OrderType.thy
 "!!A B. [| b:B;  well_ord(A,r);  well_ord(B,s) |] ==>  \
\        ordertype(pred(A+B, Inr(b), radd(A,r,B,s)), radd(A,r,B,s)) = \
\        ordertype(A+pred(B,b,s), radd(A,r,pred(B,b,s),s))";
by (resolve_tac [pred_Inr_bij RS ord_isoI RS ord_iso_sym RS ordertype_eq] 1);
by (fast_tac (sum_cs addss (radd_ss addsimps [pred_def, id_def])) 2);
by (REPEAT_FIRST (ares_tac [well_ord_radd, pred_subset, well_ord_subset]));
qed "ordertype_pred_Inr_eq";

(*** Basic laws for ordinal addition ***)

goalw OrderType.thy [oadd_def] 
    "!!i j. [| Ord(i);  Ord(j) |] ==> Ord(i++j)";
by (REPEAT (ares_tac [Ord_ordertype, well_ord_radd, well_ord_Memrel] 1));
qed "Ord_oadd";

(** Ordinal addition with zero **)

goalw OrderType.thy [oadd_def] "!!i. Ord(i) ==> i++0 = i";
by (asm_simp_tac (ZF_ss addsimps [Memrel_0, ordertype_sum_0_eq, 
                                  ordertype_Memrel, well_ord_Memrel]) 1);
qed "oadd_0";

goalw OrderType.thy [oadd_def] "!!i. Ord(i) ==> 0++i = i";
by (asm_simp_tac (ZF_ss addsimps [Memrel_0, ordertype_0_sum_eq, 
                                  ordertype_Memrel, well_ord_Memrel]) 1);
qed "oadd_0_left";


(*** Further properties of ordinal addition.  Statements by Grabczewski,
    proofs by lcp. ***)

goalw OrderType.thy [oadd_def] "!!i j k. [| k<i;  Ord(j) |] ==> k < i++j";
by (rtac ltE 1 THEN assume_tac 1);
by (rtac ltI 1);
by (REPEAT (ares_tac [Ord_ordertype, well_ord_radd, well_ord_Memrel] 2));
by (asm_simp_tac 
    (ZF_ss addsimps [ordertype_pred_unfold, 
                     well_ord_radd, well_ord_Memrel,
                     ordertype_pred_Inl_eq, 
                     lt_pred_Memrel, leI RS le_ordertype_Memrel]
           setloop rtac (InlI RSN (2,RepFun_eqI))) 1);
qed "lt_oadd1";

(*Thus also we obtain the rule  i++j = k ==> i le k *)
goal OrderType.thy "!!i j. [| Ord(i);  Ord(j) |] ==> i le i++j";
by (rtac all_lt_imp_le 1);
by (REPEAT (ares_tac [Ord_oadd, lt_oadd1] 1));
qed "oadd_le_self";

(** A couple of strange but necessary results! **)

goal OrderType.thy
    "!!A B. A<=B ==> id(A) : ord_iso(A, Memrel(A), A, Memrel(B))";
by (resolve_tac [id_bij RS ord_isoI] 1);
by (asm_simp_tac (ZF_ss addsimps [id_conv, Memrel_iff]) 1);
by (fast_tac ZF_cs 1);
qed "id_ord_iso_Memrel";

goal OrderType.thy
    "!!k. [| well_ord(A,r);  k<j |] ==>                 \
\            ordertype(A+k, radd(A, r, k, Memrel(j))) = \
\            ordertype(A+k, radd(A, r, k, Memrel(k)))";
by (etac ltE 1);
by (resolve_tac [ord_iso_refl RS sum_ord_iso_cong RS ordertype_eq] 1);
by (eresolve_tac [OrdmemD RS id_ord_iso_Memrel RS ord_iso_sym] 1);
by (REPEAT_FIRST (ares_tac [well_ord_radd, well_ord_Memrel]));
qed "ordertype_sum_Memrel";

goalw OrderType.thy [oadd_def] "!!i j k. [| k<j;  Ord(i) |] ==> i++k < i++j";
by (rtac ltE 1 THEN assume_tac 1);
by (resolve_tac [ordertype_pred_unfold RS equalityD2 RS subsetD RS ltI] 1);
by (REPEAT_FIRST (ares_tac [Ord_ordertype, well_ord_radd, well_ord_Memrel]));
by (rtac RepFun_eqI 1);
by (etac InrI 2);
by (asm_simp_tac 
    (ZF_ss addsimps [ordertype_pred_Inr_eq, well_ord_Memrel, 
                     lt_pred_Memrel, leI RS le_ordertype_Memrel,
                     ordertype_sum_Memrel]) 1);
qed "oadd_lt_mono2";

goal OrderType.thy
    "!!i j k. [| i++j < i++k;  Ord(i);  Ord(j); Ord(k) |] ==> j<k";
by (rtac Ord_linear_lt 1);
by (REPEAT_SOME assume_tac);
by (ALLGOALS
    (fast_tac (ZF_cs addDs [oadd_lt_mono2] addEs [lt_irrefl, lt_asym])));
qed "oadd_lt_cancel2";

goal OrderType.thy
    "!!i j k. [| Ord(i); Ord(j); Ord(k) |] ==> i++j < i++k <-> j<k";
by (fast_tac (ZF_cs addSIs [oadd_lt_mono2] addSEs [oadd_lt_cancel2]) 1);
qed "oadd_lt_iff2";

goal OrderType.thy
    "!!i j k. [| i++j = i++k;  Ord(i);  Ord(j); Ord(k) |] ==> j=k";
by (rtac Ord_linear_lt 1);
by (REPEAT_SOME assume_tac);
by (ALLGOALS
    (fast_tac (ZF_cs addDs [oadd_lt_mono2] 
                     addss (ZF_ss addsimps [lt_not_refl]))));
qed "oadd_inject";

goalw OrderType.thy [oadd_def] 
    "!!i j k. [| k < i++j;  Ord(i);  Ord(j) |] ==> k<i | (EX l:j. k = i++l )";
(*Rotate the hypotheses so that simplification will work*)
by (etac revcut_rl 1);
by (asm_full_simp_tac 
    (ZF_ss addsimps [ordertype_pred_unfold, well_ord_radd,
                     well_ord_Memrel]) 1);
by (eresolve_tac [ltD RS RepFunE] 1);
by (fast_tac (sum_cs addss 
              (ZF_ss addsimps [ordertype_pred_Inl_eq, well_ord_Memrel, 
                               ltI, lt_pred_Memrel, le_ordertype_Memrel, leI,
                               ordertype_pred_Inr_eq, 
                               ordertype_sum_Memrel])) 1);
qed "lt_oadd_disj";


(*** Ordinal addition with successor -- via associativity! ***)

goalw OrderType.thy [oadd_def]
    "!!i j k. [| Ord(i);  Ord(j);  Ord(k) |] ==> (i++j)++k = i++(j++k)";
by (resolve_tac [ordertype_eq RS trans] 1);
by (rtac ([ordertype_ord_iso RS ord_iso_sym, ord_iso_refl] MRS 
          sum_ord_iso_cong) 1);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel, Ord_ordertype] 1));
by (resolve_tac [sum_assoc_ord_iso RS ordertype_eq RS trans] 1);
by (rtac ([ord_iso_refl, ordertype_ord_iso] MRS sum_ord_iso_cong RS 
          ordertype_eq) 2);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel, Ord_ordertype] 1));
qed "oadd_assoc";

goal OrderType.thy
    "!!i j. [| Ord(i);  Ord(j) |] ==> i++j = i Un (UN k:j. {i++k})";
by (rtac (subsetI RS equalityI) 1);
by (eresolve_tac [ltI RS lt_oadd_disj RS disjE] 1);
by (REPEAT (ares_tac [Ord_oadd] 1));
by (fast_tac (ZF_cs addIs [lt_oadd1, oadd_lt_mono2]
                    addss (ZF_ss addsimps [Ord_mem_iff_lt, Ord_oadd])) 3);
by (fast_tac ZF_cs 2);
by (fast_tac (ZF_cs addSEs [ltE]) 1);
qed "oadd_unfold";

goal OrderType.thy "!!i. Ord(i) ==> i++1 = succ(i)";
by (asm_simp_tac (ZF_ss addsimps [oadd_unfold, Ord_1, oadd_0]) 1);
by (fast_tac eq_cs 1);
qed "oadd_1";

goal OrderType.thy
    "!!i. [| Ord(i);  Ord(j) |] ==> i++succ(j) = succ(i++j)";
by (asm_simp_tac 
    (ZF_ss addsimps [oadd_1 RS sym, Ord_oadd, oadd_assoc, Ord_1]) 1);
qed "oadd_succ";


(** Ordinal addition with limit ordinals **)

val prems = goal OrderType.thy
    "[| Ord(i);  !!x. x:A ==> Ord(j(x));  a:A |] ==> \
\    i ++ (UN x:A. j(x)) = (UN x:A. i++j(x))";
by (fast_tac (eq_cs addIs (prems @ [ltI, Ord_UN, Ord_oadd, 
                                    lt_oadd1 RS ltD, oadd_lt_mono2 RS ltD])
                     addSEs [ltE, ltI RS lt_oadd_disj RS disjE]) 1);
qed "oadd_UN";

goal OrderType.thy 
    "!!i j. [| Ord(i);  Limit(j) |] ==> i++j = (UN k:j. i++k)";
by (forward_tac [Limit_has_0 RS ltD] 1);
by (asm_simp_tac (ZF_ss addsimps [Limit_is_Ord RS Ord_in_Ord,
                                  oadd_UN RS sym, Union_eq_UN RS sym, 
                                  Limit_Union_eq]) 1);
qed "oadd_Limit";

(** Order/monotonicity properties of ordinal addition **)

goal OrderType.thy "!!i j. [| Ord(i);  Ord(j) |] ==> i le j++i";
by (eres_inst_tac [("i","i")] trans_induct3 1);
by (asm_simp_tac (ZF_ss addsimps [oadd_0, Ord_0_le]) 1);
by (asm_simp_tac (ZF_ss addsimps [oadd_succ, succ_leI]) 1);
by (asm_simp_tac (ZF_ss addsimps [oadd_Limit]) 1);
by (rtac le_trans 1);
by (rtac le_implies_UN_le_UN 2);
by (fast_tac ZF_cs 2);
by (asm_simp_tac (ZF_ss addsimps [Union_eq_UN RS sym, Limit_Union_eq, 
                                  le_refl, Limit_is_Ord]) 1);
qed "oadd_le_self2";

goal OrderType.thy "!!i j k. [| k le j;  Ord(i) |] ==> k++i le j++i";
by (forward_tac [lt_Ord] 1);
by (forward_tac [le_Ord2] 1);
by (etac trans_induct3 1);
by (asm_simp_tac (ZF_ss addsimps [oadd_0]) 1);
by (asm_simp_tac (ZF_ss addsimps [oadd_succ, succ_le_iff]) 1);
by (asm_simp_tac (ZF_ss addsimps [oadd_Limit]) 1);
by (rtac le_implies_UN_le_UN 1);
by (fast_tac ZF_cs 1);
qed "oadd_le_mono1";

goal OrderType.thy "!!i j. [| i' le i;  j'<j |] ==> i'++j' < i++j";
by (rtac lt_trans1 1);
by (REPEAT (eresolve_tac [asm_rl, oadd_le_mono1, oadd_lt_mono2, ltE,
                          Ord_succD] 1));
qed "oadd_lt_mono";

goal OrderType.thy "!!i j. [| i' le i;  j' le j |] ==> i'++j' le i++j";
by (asm_simp_tac (ZF_ss addsimps [oadd_succ RS sym, le_Ord2, oadd_lt_mono]) 1);
qed "oadd_le_mono";

goal OrderType.thy
    "!!i j k. [| Ord(i); Ord(j); Ord(k) |] ==> i++j le i++k <-> j le k";
by (asm_simp_tac (ZF_ss addsimps [oadd_lt_iff2, oadd_succ RS sym, 
                                  Ord_succ]) 1);
qed "oadd_le_iff2";


(** Ordinal subtraction; the difference is ordertype(j-i, Memrel(j)). 
    Probably simpler to define the difference recursively!
**)

goal OrderType.thy
    "!!A B. A<=B ==> (lam y:B. if(y:A, Inl(y), Inr(y))) : bij(B, A+(B-A))";
by (res_inst_tac [("d", "case(%x.x, %y.y)")] lam_bijective 1);
by (fast_tac (sum_cs addSIs [if_type]) 1);
by (fast_tac (ZF_cs addSIs [case_type]) 1);
by (etac sumE 2);
by (ALLGOALS (asm_simp_tac (sum_ss setloop split_tac [expand_if])));
qed "bij_sum_Diff";

goal OrderType.thy
    "!!i j. i le j ==>  \
\           ordertype(i+(j-i), radd(i,Memrel(j),j-i,Memrel(j))) =       \
\           ordertype(j, Memrel(j))";
by (safe_tac (ZF_cs addSDs [le_subset_iff RS iffD1]));
by (resolve_tac [bij_sum_Diff RS ord_isoI RS ord_iso_sym RS ordertype_eq] 1);
by (etac well_ord_Memrel 3);
by (assume_tac 1);
by (asm_simp_tac 
     (radd_ss setloop split_tac [expand_if] addsimps [Memrel_iff]) 1);
by (forw_inst_tac [("j", "y")] Ord_in_Ord 1 THEN assume_tac 1);
by (forw_inst_tac [("j", "x")] Ord_in_Ord 1 THEN assume_tac 1);
by (asm_simp_tac (ZF_ss addsimps [Ord_mem_iff_lt, lt_Ord, not_lt_iff_le]) 1);
by (fast_tac (ZF_cs addEs [lt_trans2, lt_trans]) 1);
qed "ordertype_sum_Diff";

goalw OrderType.thy [oadd_def, odiff_def]
    "!!i j. i le j ==>  \
\           i ++ (j--i) = ordertype(i+(j-i), radd(i,Memrel(j),j-i,Memrel(j)))";
by (safe_tac (ZF_cs addSDs [le_subset_iff RS iffD1]));
by (resolve_tac [sum_ord_iso_cong RS ordertype_eq] 1);
by (etac id_ord_iso_Memrel 1);
by (resolve_tac [ordertype_ord_iso RS ord_iso_sym] 1);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel RS well_ord_subset,
                      Diff_subset] 1));
qed "oadd_ordertype_Diff";

goal OrderType.thy "!!i j. i le j ==> i ++ (j--i) = j";
by (asm_simp_tac (ZF_ss addsimps [oadd_ordertype_Diff, ordertype_sum_Diff, 
                                  ordertype_Memrel, lt_Ord2 RS Ord_succD]) 1);
qed "oadd_odiff_inverse";

goalw OrderType.thy [odiff_def] 
    "!!i j. [| Ord(i);  Ord(j) |] ==> Ord(i--j)";
by (REPEAT (ares_tac [Ord_ordertype, well_ord_Memrel RS well_ord_subset, 
                      Diff_subset] 1));
qed "Ord_odiff";

(*By oadd_inject, the difference between i and j is unique.  Note that we get
  i++j = k  ==>  j = k--i.  *)
goal OrderType.thy
    "!!i j. [| Ord(i); Ord(j) |] ==> (i++j) -- i = j";
by (rtac oadd_inject 1);
by (REPEAT (ares_tac [Ord_ordertype, Ord_oadd, Ord_odiff] 2));
by (asm_simp_tac (ZF_ss addsimps [oadd_odiff_inverse, oadd_le_self]) 1);
qed "odiff_oadd_inverse";

val [i_lt_j, k_le_i] = goal OrderType.thy
    "[| i<j;  k le i |] ==> i--k < j--k";
by (rtac (k_le_i RS lt_Ord RSN (2,oadd_lt_cancel2)) 1);
by (simp_tac
    (ZF_ss addsimps [i_lt_j, k_le_i, [k_le_i, leI] MRS le_trans,
                     oadd_odiff_inverse]) 1);
by (REPEAT (resolve_tac (Ord_odiff :: 
                         ([i_lt_j, k_le_i] RL [lt_Ord, lt_Ord2])) 1));
qed "odiff_lt_mono2";


(**** Ordinal Multiplication ****)

goalw OrderType.thy [omult_def] 
    "!!i j. [| Ord(i);  Ord(j) |] ==> Ord(i**j)";
by (REPEAT (ares_tac [Ord_ordertype, well_ord_rmult, well_ord_Memrel] 1));
qed "Ord_omult";

(*** A useful unfolding law ***)

goalw OrderType.thy [pred_def]
 "!!A B. [| a:A;  b:B |] ==>  \
\        pred(A*B, <a,b>, rmult(A,r,B,s)) =     \
\        pred(A,a,r)*B Un ({a} * pred(B,b,s))";
by (safe_tac eq_cs);
by (ALLGOALS (asm_full_simp_tac (ZF_ss addsimps [rmult_iff])));
by (ALLGOALS (fast_tac ZF_cs));
qed "pred_Pair_eq";

goal OrderType.thy
 "!!A B. [| a:A;  b:B;  well_ord(A,r);  well_ord(B,s) |] ==>  \
\        ordertype(pred(A*B, <a,b>, rmult(A,r,B,s)), rmult(A,r,B,s)) = \
\        ordertype(pred(A,a,r)*B + pred(B,b,s),                 \
\                 radd(A*B, rmult(A,r,B,s), B, s))";
by (asm_simp_tac (ZF_ss addsimps [pred_Pair_eq]) 1);
by (resolve_tac [ordertype_eq RS sym] 1);
by (rtac prod_sum_singleton_ord_iso 1);
by (REPEAT_FIRST (ares_tac [pred_subset, well_ord_rmult RS well_ord_subset]));
by (fast_tac (ZF_cs addSEs [predE]) 1);
qed "ordertype_pred_Pair_eq";

goalw OrderType.thy [oadd_def, omult_def]
 "!!i j. [| i'<i;  j'<j |] ==>  \
\        ordertype(pred(i*j, <i',j'>, rmult(i,Memrel(i),j,Memrel(j))), \
\                  rmult(i,Memrel(i),j,Memrel(j))) = \
\        j**i' ++ j'";
by (asm_simp_tac (ZF_ss addsimps [ordertype_pred_Pair_eq, lt_pred_Memrel, 
                                  ltD, lt_Ord2, well_ord_Memrel]) 1);
by (rtac trans 1);
by (resolve_tac [ordertype_ord_iso RS sum_ord_iso_cong RS ordertype_eq] 2);
by (rtac ord_iso_refl 3);
by (resolve_tac [id_bij RS ord_isoI RS ordertype_eq] 1);
by (REPEAT_FIRST (eresolve_tac [SigmaE, sumE, ltE, ssubst]));
by (REPEAT_FIRST (ares_tac [well_ord_rmult, well_ord_radd, well_ord_Memrel, 
                            Ord_ordertype]));
by (ALLGOALS 
    (asm_simp_tac (radd_ss addsimps [rmult_iff, id_conv, Memrel_iff])));
by (safe_tac ZF_cs);
by (ALLGOALS (fast_tac (ZF_cs addEs [Ord_trans])));
qed "ordertype_pred_Pair_lemma";

goalw OrderType.thy [omult_def]
 "!!i j. [| Ord(i);  Ord(j);  k<j**i |] ==>  \
\        EX j' i'. k = j**i' ++ j' & j'<j & i'<i";
by (asm_full_simp_tac (ZF_ss addsimps [ordertype_pred_unfold, 
                                       well_ord_rmult, well_ord_Memrel]) 1);
by (step_tac (ZF_cs addSEs [ltE]) 1);
by (asm_simp_tac (ZF_ss addsimps [ordertype_pred_Pair_lemma, ltI,
                                  symmetric omult_def]) 1);
by (fast_tac (ZF_cs addIs [ltI]) 1);
qed "lt_omult";

goalw OrderType.thy [omult_def]
 "!!i j. [| j'<j;  i'<i |] ==> j**i' ++ j'  <  j**i";
by (rtac ltI 1);
by (asm_simp_tac
    (ZF_ss addsimps [Ord_ordertype, well_ord_rmult, well_ord_Memrel, 
                     lt_Ord2]) 2);
by (asm_simp_tac 
    (ZF_ss addsimps [ordertype_pred_unfold, 
                     well_ord_rmult, well_ord_Memrel, lt_Ord2]) 1);
by (rtac RepFun_eqI 1);
by (fast_tac (ZF_cs addSEs [ltE]) 2);
by (asm_simp_tac 
    (ZF_ss addsimps [ordertype_pred_Pair_lemma, ltI, symmetric omult_def]) 1);
qed "omult_oadd_lt";

goal OrderType.thy
 "!!i j. [| Ord(i);  Ord(j) |] ==> j**i = (UN j':j. UN i':i. {j**i' ++ j'})";
by (rtac (subsetI RS equalityI) 1);
by (resolve_tac [lt_omult RS exE] 1);
by (etac ltI 3);
by (REPEAT (ares_tac [Ord_omult] 1));
by (fast_tac (ZF_cs addSEs [ltE]) 1);
by (fast_tac (ZF_cs addIs [omult_oadd_lt RS ltD, ltI]) 1);
qed "omult_unfold";

(*** Basic laws for ordinal multiplication ***)

(** Ordinal multiplication by zero **)

goalw OrderType.thy [omult_def] "i**0 = 0";
by (asm_simp_tac (ZF_ss addsimps [ordertype_0]) 1);
qed "omult_0";

goalw OrderType.thy [omult_def] "0**i = 0";
by (asm_simp_tac (ZF_ss addsimps [ordertype_0]) 1);
qed "omult_0_left";

(** Ordinal multiplication by 1 **)

goalw OrderType.thy [omult_def] "!!i. Ord(i) ==> i**1 = i";
by (resolve_tac [ord_isoI RS ordertype_eq RS trans] 1);
by (res_inst_tac [("c", "snd"), ("d", "%z.<0,z>")] lam_bijective 1);
by (REPEAT_FIRST (eresolve_tac [snd_type, SigmaE, succE, emptyE, 
                                well_ord_Memrel, ordertype_Memrel]));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps [rmult_iff, Memrel_iff])));
qed "omult_1";

goalw OrderType.thy [omult_def] "!!i. Ord(i) ==> 1**i = i";
by (resolve_tac [ord_isoI RS ordertype_eq RS trans] 1);
by (res_inst_tac [("c", "fst"), ("d", "%z.<z,0>")] lam_bijective 1);
by (REPEAT_FIRST (eresolve_tac [fst_type, SigmaE, succE, emptyE, 
                                well_ord_Memrel, ordertype_Memrel]));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps [rmult_iff, Memrel_iff])));
qed "omult_1_left";

(** Distributive law for ordinal multiplication and addition **)

goalw OrderType.thy [omult_def, oadd_def]
    "!!i. [| Ord(i);  Ord(j);  Ord(k) |] ==> i**(j++k) = (i**j)++(i**k)";
by (resolve_tac [ordertype_eq RS trans] 1);
by (rtac ([ordertype_ord_iso RS ord_iso_sym, ord_iso_refl] MRS 
          prod_ord_iso_cong) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_radd, well_ord_Memrel, 
                      Ord_ordertype] 1));
by (rtac (sum_prod_distrib_ord_iso RS ordertype_eq RS trans) 1);
by (rtac ordertype_eq 2);
by (rtac ([ordertype_ord_iso, ordertype_ord_iso] MRS sum_ord_iso_cong) 2);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_radd, well_ord_Memrel, 
                      Ord_ordertype] 1));
qed "oadd_omult_distrib";

goal OrderType.thy "!!i. [| Ord(i);  Ord(j) |] ==> i**succ(j) = (i**j)++i";
by (asm_simp_tac 
    (ZF_ss addsimps [oadd_1 RS sym, omult_1, oadd_omult_distrib, Ord_1]) 1);
qed "omult_succ";

(** Associative law **)

goalw OrderType.thy [omult_def]
    "!!i j k. [| Ord(i);  Ord(j);  Ord(k) |] ==> (i**j)**k = i**(j**k)";
by (resolve_tac [ordertype_eq RS trans] 1);
by (rtac ([ord_iso_refl, ordertype_ord_iso RS ord_iso_sym] MRS 
          prod_ord_iso_cong) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
by (resolve_tac [prod_assoc_ord_iso RS ord_iso_sym RS 
                 ordertype_eq RS trans] 1);
by (rtac ([ordertype_ord_iso, ord_iso_refl] MRS prod_ord_iso_cong RS
          ordertype_eq) 2);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel, Ord_ordertype] 1));
qed "omult_assoc";


(** Ordinal multiplication with limit ordinals **)

val prems = goal OrderType.thy
    "[| Ord(i);  !!x. x:A ==> Ord(j(x)) |] ==> \
\    i ** (UN x:A. j(x)) = (UN x:A. i**j(x))";
by (asm_simp_tac (ZF_ss addsimps (prems@[Ord_UN, omult_unfold])) 1);
by (fast_tac eq_cs 1);
qed "omult_UN";

goal OrderType.thy 
    "!!i j. [| Ord(i);  Limit(j) |] ==> i**j = (UN k:j. i**k)";
by (asm_simp_tac 
    (ZF_ss addsimps [Limit_is_Ord RS Ord_in_Ord, omult_UN RS sym, 
                     Union_eq_UN RS sym, Limit_Union_eq]) 1);
qed "omult_Limit";


(*** Ordering/monotonicity properties of ordinal multiplication ***)

(*As a special case we have "[| 0<i;  0<j |] ==> 0 < i**j" *)
goal OrderType.thy "!!i j. [| k<i;  0<j |] ==> k < i**j";
by (safe_tac (ZF_cs addSEs [ltE] addSIs [ltI, Ord_omult]));
by (asm_simp_tac (ZF_ss addsimps [omult_unfold]) 1);
by (REPEAT (etac UN_I 1));
by (asm_simp_tac (ZF_ss addsimps [omult_0, oadd_0_left]) 1);
qed "lt_omult1";

goal OrderType.thy "!!i j. [| Ord(i);  0<j |] ==> i le i**j";
by (rtac all_lt_imp_le 1);
by (REPEAT (ares_tac [Ord_omult, lt_omult1, lt_Ord2] 1));
qed "omult_le_self";

goal OrderType.thy "!!i j k. [| k le j;  Ord(i) |] ==> k**i le j**i";
by (forward_tac [lt_Ord] 1);
by (forward_tac [le_Ord2] 1);
by (etac trans_induct3 1);
by (asm_simp_tac (ZF_ss addsimps [omult_0, le_refl, Ord_0]) 1);
by (asm_simp_tac (ZF_ss addsimps [omult_succ, oadd_le_mono]) 1);
by (asm_simp_tac (ZF_ss addsimps [omult_Limit]) 1);
by (rtac le_implies_UN_le_UN 1);
by (fast_tac ZF_cs 1);
qed "omult_le_mono1";

goal OrderType.thy "!!i j k. [| k<j;  0<i |] ==> i**k < i**j";
by (rtac ltI 1);
by (asm_simp_tac (ZF_ss addsimps [omult_unfold, lt_Ord2]) 1);
by (safe_tac (ZF_cs addSEs [ltE] addSIs [Ord_omult]));
by (REPEAT (etac UN_I 1));
by (asm_simp_tac (ZF_ss addsimps [omult_0, oadd_0, Ord_omult]) 1);
qed "omult_lt_mono2";

goal OrderType.thy "!!i j k. [| k le j;  Ord(i) |] ==> i**k le i**j";
by (rtac subset_imp_le 1);
by (safe_tac (ZF_cs addSEs [ltE, make_elim Ord_succD] addSIs [Ord_omult]));
by (asm_full_simp_tac (ZF_ss addsimps [omult_unfold]) 1);
by (deepen_tac (ZF_cs addEs [Ord_trans, UN_I]) 0 1);
qed "omult_le_mono2";

goal OrderType.thy "!!i j. [| i' le i;  j' le j |] ==> i'**j' le i**j";
by (rtac le_trans 1);
by (REPEAT (eresolve_tac [asm_rl, omult_le_mono1, omult_le_mono2, ltE,
                          Ord_succD] 1));
qed "omult_le_mono";

goal OrderType.thy
      "!!i j. [| i' le i;  j'<j;  0<i |] ==> i'**j' < i**j";
by (rtac lt_trans1 1);
by (REPEAT (eresolve_tac [asm_rl, omult_le_mono1, omult_lt_mono2, ltE,
                          Ord_succD] 1));
qed "omult_lt_mono";

goal OrderType.thy "!!i j. [| Ord(i);  0<j |] ==> i le j**i";
by (forward_tac [lt_Ord2] 1);
by (eres_inst_tac [("i","i")] trans_induct3 1);
by (asm_simp_tac (ZF_ss addsimps [omult_0, Ord_0 RS le_refl]) 1);
by (asm_simp_tac (ZF_ss addsimps [omult_succ, succ_le_iff]) 1);
by (etac lt_trans1 1);
by (res_inst_tac [("b", "j**x")] (oadd_0 RS subst) 1 THEN 
    rtac oadd_lt_mono2 2);
by (REPEAT (ares_tac [Ord_omult] 1));
by (asm_simp_tac (ZF_ss addsimps [omult_Limit]) 1);
by (rtac le_trans 1);
by (rtac le_implies_UN_le_UN 2);
by (fast_tac ZF_cs 2);
by (asm_simp_tac (ZF_ss addsimps [Union_eq_UN RS sym, Limit_Union_eq, 
                                  Limit_is_Ord RS le_refl]) 1);
qed "omult_le_self2";


(** Further properties of ordinal multiplication **)

goal OrderType.thy "!!i j. [| i**j = i**k;  0<i;  Ord(j);  Ord(k) |] ==> j=k";
by (rtac Ord_linear_lt 1);
by (REPEAT_SOME assume_tac);
by (ALLGOALS
    (fast_tac (ZF_cs addDs [omult_lt_mono2] 
                     addss (ZF_ss addsimps [lt_not_refl]))));
qed "omult_inject";


