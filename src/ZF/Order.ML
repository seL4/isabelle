(*  Title: 	ZF/Order.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Orders in Zermelo-Fraenkel Set Theory 

Results from the book "Set Theory: an Introduction to Independence Proofs"
	by Ken Kunen.  Chapter 1, section 6.
*)

open Order;

val bij_apply_cs = ZF_cs addSEs [bij_converse_bij]
                         addIs  [bij_is_fun, apply_type];

(** Basic properties of the definitions **)

(*needed?*)
goalw Order.thy [part_ord_def, irrefl_def, trans_on_def, asym_def]
    "!!r. part_ord(A,r) ==> asym(r Int A*A)";
by (fast_tac ZF_cs 1);
qed "part_ord_Imp_asym";

val major::premx::premy::prems = goalw Order.thy [linear_def]
    "[| linear(A,r);  x:A;  y:A;  \
\       <x,y>:r ==> P;  x=y ==> P;  <y,x>:r ==> P |] ==> P";
by (cut_facts_tac [major,premx,premy] 1);
by (REPEAT_FIRST (eresolve_tac [ballE,disjE]));
by (EVERY1 (map etac prems));
by (ALLGOALS contr_tac);
qed "linearE";

(*Does the case analysis, deleting linear(A,r) and proving trivial subgoals*)
val linear_case_tac =
    SELECT_GOAL (EVERY [etac linearE 1, assume_tac 1, assume_tac 1,
			REPEAT_SOME (assume_tac ORELSE' contr_tac)]);

(** General properties of well_ord **)

goalw Order.thy [irrefl_def, part_ord_def, tot_ord_def, 
		 trans_on_def, well_ord_def]
    "!!r. [| wf[A](r); linear(A,r) |] ==> well_ord(A,r)";
by (asm_simp_tac (ZF_ss addsimps [wf_on_not_refl]) 1);
by (safe_tac ZF_cs);
by (linear_case_tac 1);
(*case x=xb*)
by (fast_tac (ZF_cs addSEs [wf_on_asym]) 1);
(*case x<xb*)
by (fast_tac (ZF_cs addSEs [wf_on_chain3]) 1);
qed "well_ordI";

goalw Order.thy [well_ord_def]
    "!!r. well_ord(A,r) ==> wf[A](r)";
by (safe_tac ZF_cs);
qed "well_ord_is_wf";

goalw Order.thy [well_ord_def, tot_ord_def, part_ord_def]
    "!!r. well_ord(A,r) ==> trans[A](r)";
by (safe_tac ZF_cs);
qed "well_ord_is_trans_on";

goalw Order.thy [well_ord_def, tot_ord_def]
  "!!r. well_ord(A,r) ==> linear(A,r)";
by (fast_tac ZF_cs 1);
qed "well_ord_is_linear";


(** Derived rules for pred(A,x,r) **)

goalw Order.thy [pred_def] "y : pred(A,x,r) <-> <y,x>:r & y:A";
by (fast_tac ZF_cs 1);
qed "pred_iff";

bind_thm ("predI", conjI RS (pred_iff RS iffD2));

val [major,minor] = goalw Order.thy [pred_def]
    "[| y: pred(A,x,r);  [| y:A; <y,x>:r |] ==> P |] ==> P";
by (rtac (major RS CollectE) 1);
by (REPEAT (ares_tac [minor] 1));
qed "predE";

goalw Order.thy [pred_def] "pred(A,x,r) <= r -`` {x}";
by (fast_tac ZF_cs 1);
qed "pred_subset_under";

goalw Order.thy [pred_def] "pred(A,x,r) <= A";
by (fast_tac ZF_cs 1);
qed "pred_subset";

goalw Order.thy [pred_def]
    "pred(pred(A,x,r), y, r) = pred(A,x,r) Int pred(A,y,r)";
by (fast_tac eq_cs 1);
qed "pred_pred_eq";

goalw Order.thy [trans_on_def, pred_def]
    "!!r. [| trans[A](r);  <y,x>:r;  x:A;  y:A \
\         |] ==> pred(pred(A,x,r), y, r) = pred(A,y,r)";
by (fast_tac eq_cs 1);
qed "trans_pred_pred_eq";

(** The ordering's properties hold over all subsets of its domain 
    [including initial segments of the form pred(A,x,r) **)

(*Note: a relation s such that s<=r need not be a partial ordering*)
goalw Order.thy [part_ord_def, irrefl_def, trans_on_def]
    "!!A B r. [| part_ord(A,r);  B<=A |] ==> part_ord(B,r)";
by (fast_tac ZF_cs 1);
qed "part_ord_subset";

goalw Order.thy [linear_def]
    "!!A B r. [| linear(A,r);  B<=A |] ==> linear(B,r)";
by (fast_tac ZF_cs 1);
qed "linear_subset";

goalw Order.thy [tot_ord_def]
    "!!A B r. [| tot_ord(A,r);  B<=A |] ==> tot_ord(B,r)";
by (fast_tac (ZF_cs addSEs [part_ord_subset, linear_subset]) 1);
qed "tot_ord_subset";

goalw Order.thy [well_ord_def]
    "!!A B r. [| well_ord(A,r);  B<=A |] ==> well_ord(B,r)";
by (fast_tac (ZF_cs addSEs [tot_ord_subset, wf_on_subset_A]) 1);
qed "well_ord_subset";


(** Order-preserving (monotone) maps **)

(*Rewriting with bijections and converse (function inverse)*)
val bij_inverse_ss = 
    ZF_ss setsolver (type_auto_tac [bij_is_fun, apply_type, 
				    bij_converse_bij, comp_fun, comp_bij])
          addsimps [right_inverse_bij, left_inverse_bij, comp_fun_apply];

goalw Order.thy [mono_map_def] 
    "!!f. f: mono_map(A,r,B,s) ==> f: A->B";
by (etac CollectD1 1);
qed "mono_map_is_fun";

goalw Order.thy [mono_map_def, inj_def] 
    "!!f. [| linear(A,r);  wf[B](s);  f: mono_map(A,r,B,s) |] ==> f: inj(A,B)";
by (step_tac ZF_cs 1);
by (linear_case_tac 1);
by (REPEAT 
    (EVERY [eresolve_tac [wf_on_not_refl RS notE] 1,
	    eresolve_tac [ssubst] 2,
	    fast_tac ZF_cs 2,
	    REPEAT (ares_tac [apply_type] 1)]));
qed "mono_map_is_inj";

(*Transitivity of similarity: the order-isomorphism relation*)
goalw Order.thy [mono_map_def] 
    "!!f. [| g: mono_map(A,r,B,s);  f: mono_map(B,s,C,t) |] ==> \
\         (f O g): mono_map(A,r,C,t)";
by (safe_tac ZF_cs);
by (ALLGOALS (asm_full_simp_tac bij_inverse_ss));
qed "mono_map_trans";


(** Order-isomorphisms -- or similarities, as Suppes calls them **)

goalw Order.thy [ord_iso_def, mono_map_def]
    "!!f. f: ord_iso(A,r,B,s) ==> f: mono_map(A,r,B,s)";
by (fast_tac (ZF_cs addSDs [bij_is_fun]) 1);
qed "ord_iso_is_mono_map";

goalw Order.thy [ord_iso_def] 
    "!!f. f: ord_iso(A,r,B,s) ==> f: bij(A,B)";
by (etac CollectD1 1);
qed "ord_iso_is_bij";

(*Needed?  But ord_iso_converse is!*)
goalw Order.thy [ord_iso_def] 
    "!!f. [| f: ord_iso(A,r,B,s);  <x,y>: r;  x:A;  y:A |] ==> \
\         <f`x, f`y> : s";
by (fast_tac ZF_cs 1);
qed "ord_iso_apply";

goalw Order.thy [ord_iso_def] 
    "!!f. [| f: ord_iso(A,r,B,s);  <x,y>: s;  x:B;  y:B |] ==> \
\         <converse(f) ` x, converse(f) ` y> : r";
by (etac CollectE 1);
by (etac (bspec RS bspec RS iffD2) 1);
by (REPEAT (eresolve_tac [asm_rl, 
			  bij_converse_bij RS bij_is_fun RS apply_type] 1));
by (asm_simp_tac (ZF_ss addsimps [right_inverse_bij]) 1);
qed "ord_iso_converse";

(*Symmetry of similarity: the order-isomorphism relation*)
goalw Order.thy [ord_iso_def] 
    "!!f. f: ord_iso(A,r,B,s) ==> converse(f): ord_iso(B,s,A,r)";
by (safe_tac ZF_cs);
by (ALLGOALS (asm_full_simp_tac bij_inverse_ss));
qed "ord_iso_sym";

(*Transitivity of similarity: the order-isomorphism relation*)
goalw Order.thy [ord_iso_def] 
    "!!f. [| g: ord_iso(A,r,B,s);  f: ord_iso(B,s,C,t) |] ==> \
\         (f O g): ord_iso(A,r,C,t)";
by (safe_tac ZF_cs);
by (ALLGOALS (asm_full_simp_tac bij_inverse_ss));
qed "ord_iso_trans";

(** Two monotone maps can make an order-isomorphism **)

goalw Order.thy [ord_iso_def, mono_map_def]
    "!!f g. [| f: mono_map(A,r,B,s);  g: mono_map(B,s,A,r);	\
\              f O g = id(B);  g O f = id(A) |] ==> f: ord_iso(A,r,B,s)";
by (safe_tac ZF_cs);
by (REPEAT_FIRST (ares_tac [fg_imp_bijective]));
by (fast_tac ZF_cs 1);
by (subgoal_tac "<g`(f`x), g`(f`y)> : r" 1);
by (fast_tac (ZF_cs addIs [apply_type] addSEs [bspec RS bspec RS mp]) 2);
by (asm_full_simp_tac 
    (ZF_ss addsimps [comp_eq_id_iff RS iffD1]) 1);
qed "mono_ord_isoI";

goal Order.thy
    "!!B. [| well_ord(A,r);  well_ord(B,s); 				\
\            f: mono_map(A,r,B,s);  converse(f): mono_map(B,s,A,r)	\
\         |] ==> f: ord_iso(A,r,B,s)";
by (REPEAT (ares_tac [mono_ord_isoI] 1));
by (forward_tac [mono_map_is_fun RS fun_is_rel] 1);
by (etac (converse_converse RS subst) 1 THEN rtac left_comp_inverse 1);
by (DEPTH_SOLVE (ares_tac [mono_map_is_inj, left_comp_inverse] 1
          ORELSE eresolve_tac [well_ord_is_linear, well_ord_is_wf] 1));
qed "well_ord_mono_ord_isoI";


(** Order-isomorphisms preserve the ordering's properties **)

goalw Order.thy [part_ord_def, irrefl_def, trans_on_def, ord_iso_def]
    "!!A B r. [| part_ord(B,s);  f: ord_iso(A,r,B,s) |] ==> part_ord(A,r)";
by (asm_simp_tac ZF_ss 1);
by (fast_tac (ZF_cs addIs [bij_is_fun RS apply_type]) 1);
qed "part_ord_ord_iso";

goalw Order.thy [linear_def, ord_iso_def]
    "!!A B r. [| linear(B,s);  f: ord_iso(A,r,B,s) |] ==> linear(A,r)";
by (asm_simp_tac ZF_ss 1);
by (safe_tac ZF_cs);
by (dres_inst_tac [("x1", "f`x"), ("x", "f`xa")] (bspec RS bspec) 1);
by (safe_tac (ZF_cs addSEs [bij_is_fun RS apply_type]));
by (dres_inst_tac [("t", "op `(converse(f))")] subst_context 1);
by (asm_full_simp_tac (ZF_ss addsimps [left_inverse_bij]) 1);
qed "linear_ord_iso";

goalw Order.thy [wf_on_def, wf_def, ord_iso_def]
    "!!A B r. [| wf[B](s);  f: ord_iso(A,r,B,s) |] ==> wf[A](r)";
(*reversed &-congruence rule handles context of membership in A*)
by (asm_full_simp_tac (ZF_ss addcongs [conj_cong2]) 1);
by (safe_tac ZF_cs);
by (dres_inst_tac [("x", "{f`z. z:Z Int A}")] spec 1);
by (safe_tac eq_cs);
by (dtac equalityD1 1);
by (fast_tac (ZF_cs addSIs [bexI]) 1);
by (fast_tac (ZF_cs addSIs [bexI]
	      addIs [bij_is_fun RS apply_type]) 1);
qed "wf_on_ord_iso";

goalw Order.thy [well_ord_def, tot_ord_def]
    "!!A B r. [| well_ord(B,s);  f: ord_iso(A,r,B,s) |] ==> well_ord(A,r)";
by (fast_tac
    (ZF_cs addSEs [part_ord_ord_iso, linear_ord_iso, wf_on_ord_iso]) 1);
qed "well_ord_ord_iso";


(*** Main results of Kunen, Chapter 1 section 6 ***)

(*Inductive argument for proving Kunen's Lemma 6.1*)
goalw Order.thy [well_ord_def, tot_ord_def, part_ord_def, pred_def]
  "!!r. [| well_ord(A,r);  x: A;  f: ord_iso(A, r, pred(A,x,r), r);  y: A |] \
\       ==> f`y = y";
by (safe_tac ZF_cs);
by (wf_on_ind_tac "y" [] 1);
by (forward_tac [ord_iso_is_bij] 1);
by (subgoal_tac "f`y1 : {y: A . <y, x> : r}" 1);
by (fast_tac (ZF_cs addSEs [bij_is_fun RS apply_type]) 2);
(*Now we know f`y1 : A  and  <f`y1, x> : r  *)
by (etac CollectE 1);
by (linear_case_tac 1);
(*Case  <f`y1, y1> : r *)   (*use induction hyp*)
by (dtac bspec 1 THEN mp_tac 2 THEN assume_tac 1);
by (dres_inst_tac [("t", "op `(converse(f))")] subst_context 1);
by (asm_full_simp_tac (ZF_ss addsimps [left_inverse_bij]) 1);
(*The case  <y1, f`y1> : r  *)
by (subgoal_tac "<y1,x> : r" 1);
by (fast_tac (ZF_cs addSEs [trans_onD]) 2);
by (dtac ord_iso_converse 1 THEN assume_tac 1 THEN fast_tac ZF_cs 2);
by (fast_tac ZF_cs 1);
by (asm_full_simp_tac (ZF_ss addsimps [left_inverse_bij]) 1);
(*now use induction hyp*)
by (dtac bspec 1 THEN mp_tac 2 THEN fast_tac bij_apply_cs 1);
by (dres_inst_tac [("t", "op `(f)")] subst_context 1);
by (asm_full_simp_tac (ZF_ss addsimps [right_inverse_bij]) 1);
qed "not_well_ord_iso_pred_lemma";


(*Kunen's Lemma 6.1: there's no order-isomorphism to an initial segment
                     of a well-ordering*)
goal Order.thy
    "!!r. [| well_ord(A,r);  f : ord_iso(A, r, pred(A,x,r), r);  x:A |] ==> P";
by (metacut_tac not_well_ord_iso_pred_lemma 1);
by (REPEAT_FIRST assume_tac);
(*Now we know f`x = x*)
by (EVERY1 [dtac (ord_iso_is_bij RS bij_is_fun RS apply_type),
	     assume_tac]);
(*Now we know f`x : pred(A,x,r) *)
by (asm_full_simp_tac (ZF_ss addsimps [well_ord_def, pred_def]) 1);
by (fast_tac (ZF_cs addSEs [wf_on_not_refl RS notE]) 1);
qed "well_ord_iso_predE";

(*Simple consequence of Lemma 6.1*)
goal Order.thy
 "!!r. [| well_ord(A,r);  f : ord_iso(pred(A,a,r), r, pred(A,c,r), r);	\
\         a:A;  c:A |] ==> a=c";
by (forward_tac [well_ord_is_trans_on] 1);
by (forward_tac [well_ord_is_linear] 1);
by (linear_case_tac 1);
by (dtac ord_iso_sym 1);
by (REPEAT   (*because there are two symmetric cases*)
    (EVERY [eresolve_tac [pred_subset RSN (2, well_ord_subset) RS
			  well_ord_iso_predE] 1,
	    fast_tac (ZF_cs addSIs [predI]) 2,
	    asm_simp_tac (ZF_ss addsimps [trans_pred_pred_eq]) 1]));
qed "well_ord_iso_pred_eq";

(*Does not assume r is a wellordering!*)
goalw Order.thy [ord_iso_def, pred_def]
 "!!r. [| f : ord_iso(A,r,B,s);	  a:A |] ==> 	\
\      f `` pred(A,a,r) = pred(B, f`a, s)";
by (etac CollectE 1);
by (asm_simp_tac 
    (ZF_ss addsimps [[bij_is_fun, Collect_subset] MRS image_fun]) 1);
by (safe_tac (eq_cs addSEs [bij_is_fun RS apply_type]));
by (resolve_tac [RepFun_eqI] 1);
by (fast_tac (ZF_cs addSIs [right_inverse_bij RS sym]) 1);
by (asm_simp_tac
    (ZF_ss addsimps [right_inverse_bij]
           setsolver type_auto_tac
	                [bij_is_fun, apply_funtype, bij_converse_bij]) 1);
qed "ord_iso_image_pred";

(*But in use, A and B may themselves be initial segments.  Then use
  trans_pred_pred_eq to simplify the pred(pred...) terms.  See just below.*)
goal Order.thy
 "!!r. [| f : ord_iso(A,r,B,s);	  a:A |] ==> 	\
\      restrict(f, pred(A,a,r)) : ord_iso(pred(A,a,r), r, pred(B, f`a, s), s)";
by (asm_simp_tac (ZF_ss addsimps [ord_iso_image_pred RS sym]) 1);
by (rewrite_goals_tac [ord_iso_def]);
by (step_tac ZF_cs 1);
by (asm_full_simp_tac (ZF_ss addsimps [pred_def]) 2);
by (asm_full_simp_tac (ZF_ss addsimps [pred_def]) 2);
by (eresolve_tac [[bij_is_inj, pred_subset] MRS restrict_bij] 1);
qed "ord_iso_restrict_pred";

(*Tricky; a lot of forward proof!*)
goal Order.thy
 "!!r. [| well_ord(A,r);  well_ord(B,s);  <a,c>: r;	\
\         f : ord_iso(pred(A,a,r), r, pred(B,b,s), s);	\
\         g : ord_iso(pred(A,c,r), r, pred(B,d,s), s);	\
\         a:A;  c:A;  b:B;  d:B |] ==> <b,d>: s";
by (forward_tac [ord_iso_is_bij RS bij_is_fun RS apply_type] 1  THEN
    REPEAT1 (eresolve_tac [asm_rl, predI, predE] 1));
by (subgoal_tac "b = g`a" 1);
by (asm_simp_tac ZF_ss 1);
by (resolve_tac [well_ord_iso_pred_eq] 1);
by (REPEAT_SOME assume_tac);
by (forward_tac [ord_iso_restrict_pred] 1  THEN
    REPEAT1 (eresolve_tac [asm_rl, predI] 1));
by (asm_full_simp_tac
    (ZF_ss addsimps [well_ord_is_trans_on, trans_pred_pred_eq]) 1);
by (eresolve_tac [ord_iso_sym RS ord_iso_trans] 1);
by (assume_tac 1);
qed "well_ord_iso_preserving";

(*Inductive argument for proving Kunen's Lemma 6.2*)
goalw Order.thy [well_ord_def, tot_ord_def, part_ord_def]
    "!!r. [| well_ord(A,r);  well_ord(B,s);  \
\            f: ord_iso(A,r, B,s);  g: ord_iso(A,r, B,s);  y: A |] \
\         ==> f`y = g`y";
by (safe_tac ZF_cs);
by (wf_on_ind_tac "y" [] 1);
by (subgoals_tac ["f: bij(A,B)", "g: bij(A,B)", "f`y1 : B", "g`y1 : B"] 1);
by (REPEAT (fast_tac (bij_apply_cs addSEs [ord_iso_is_bij]) 2));
by (linear_case_tac 1);
(*The case  <f`y1, g`y1> : s  *)
by (forw_inst_tac [("f","g")] ord_iso_converse 1 THEN REPEAT (assume_tac 1));
by (asm_full_simp_tac (ZF_ss addsimps [left_inverse_bij]) 1);
by (dtac bspec 1 THEN mp_tac 2 THEN fast_tac bij_apply_cs 1);
by (dres_inst_tac [("t", "op `(converse(f))")] subst_context 1);
by (dres_inst_tac [("t", "op `(g)")] subst_context 1);
by (asm_full_simp_tac bij_inverse_ss 1);
(*The case  <g`y1, f`y1> : s  *)
by (forw_inst_tac [("f","f")] ord_iso_converse 1 THEN REPEAT (assume_tac 1));
by (asm_full_simp_tac (ZF_ss addsimps [left_inverse_bij]) 1);
by (dtac bspec 1 THEN mp_tac 2 THEN fast_tac bij_apply_cs 1);
by (dres_inst_tac [("t", "op `(converse(g))")] subst_context 1);
by (dres_inst_tac [("t", "op `(f)")] subst_context 1);
by (asm_full_simp_tac bij_inverse_ss 1);
qed "well_ord_iso_unique_lemma";

(*Kunen's Lemma 6.2: Order-isomorphisms between well-orderings are unique*)
goal Order.thy
    "!!r. [| well_ord(B,s);  \
\            f: ord_iso(A,r, B,s);  g: ord_iso(A,r, B,s) |] ==> f = g";
by (rtac fun_extension 1);
by (etac (ord_iso_is_bij RS bij_is_fun) 1);
by (etac (ord_iso_is_bij RS bij_is_fun) 1);
by (rtac well_ord_iso_unique_lemma 1);
by (REPEAT_SOME (eresolve_tac [asm_rl, well_ord_ord_iso]));
qed "well_ord_iso_unique";


(** Towards Kunen's Theorem 6.3: linearity of the similarity relation **)

goalw Order.thy [ord_iso_map_def]
    "ord_iso_map(A,r,B,s) <= A*B";
by (fast_tac ZF_cs 1);
qed "ord_iso_map_subset";

goalw Order.thy [ord_iso_map_def]
    "domain(ord_iso_map(A,r,B,s)) <= A";
by (fast_tac ZF_cs 1);
qed "domain_ord_iso_map";

goalw Order.thy [ord_iso_map_def]
    "range(ord_iso_map(A,r,B,s)) <= B";
by (fast_tac ZF_cs 1);
qed "range_ord_iso_map";

goalw Order.thy [ord_iso_map_def]
    "converse(ord_iso_map(A,r,B,s)) = ord_iso_map(B,s,A,r)";
by (fast_tac (eq_cs addIs [ord_iso_sym]) 1);
qed "converse_ord_iso_map";

goalw Order.thy [ord_iso_map_def, function_def]
    "!!B. well_ord(B,s) ==> function(ord_iso_map(A,r,B,s))";
by (safe_tac ZF_cs);
by (resolve_tac [well_ord_iso_pred_eq] 1);
by (REPEAT_SOME assume_tac);
by (eresolve_tac [ord_iso_sym RS ord_iso_trans] 1);
by (assume_tac 1);
qed "function_ord_iso_map";

goal Order.thy
    "!!B. well_ord(B,s) ==> ord_iso_map(A,r,B,s) 	\
\          : domain(ord_iso_map(A,r,B,s)) -> range(ord_iso_map(A,r,B,s))";
by (asm_simp_tac 
    (ZF_ss addsimps [Pi_iff, function_ord_iso_map,
		     ord_iso_map_subset RS domain_times_range]) 1);
qed "ord_iso_map_fun";

goalw Order.thy [mono_map_def]
    "!!B. [| well_ord(A,r);  well_ord(B,s) |] ==> ord_iso_map(A,r,B,s) 	\
\          : mono_map(domain(ord_iso_map(A,r,B,s)), r, 	\
\	              range(ord_iso_map(A,r,B,s)), s)";
by (asm_simp_tac (ZF_ss addsimps [ord_iso_map_fun]) 1);
by (safe_tac ZF_cs);
by (subgoals_tac ["x:A", "xa:A", "y:B", "ya:B"] 1);
by (REPEAT 
    (fast_tac (ZF_cs addSEs [ord_iso_map_subset RS subsetD RS SigmaE]) 2));
by (asm_simp_tac (ZF_ss addsimps [ord_iso_map_fun RSN (2,apply_equality)]) 1);
by (rewrite_goals_tac [ord_iso_map_def]);
by (safe_tac (ZF_cs addSEs [UN_E]));
by (resolve_tac [well_ord_iso_preserving] 1 THEN REPEAT_FIRST assume_tac);
qed "ord_iso_map_mono_map";

goalw Order.thy [mono_map_def]
    "!!B. [| well_ord(A,r);  well_ord(B,s) |] ==> ord_iso_map(A,r,B,s) 	\
\          : ord_iso(domain(ord_iso_map(A,r,B,s)), r, 	\
\	              range(ord_iso_map(A,r,B,s)), s)";
by (resolve_tac [well_ord_mono_ord_isoI] 1);
by (resolve_tac [converse_ord_iso_map RS subst] 4);
by (asm_simp_tac 
    (ZF_ss addsimps [ord_iso_map_subset RS converse_converse, 
		     domain_converse, range_converse]) 4);
by (REPEAT (ares_tac [ord_iso_map_mono_map] 3));
by (ALLGOALS (etac well_ord_subset));
by (ALLGOALS (resolve_tac [domain_ord_iso_map, range_ord_iso_map]));
qed "ord_iso_map_ord_iso";

(*One way of saying that domain(ord_iso_map(A,r,B,s)) is downwards-closed*)
goalw Order.thy [ord_iso_map_def]
  "!!B. [| well_ord(A,r);  well_ord(B,s);    		\
\          x: A;  x ~: domain(ord_iso_map(A,r,B,s)) 	\
\       |] ==>  domain(ord_iso_map(A,r,B,s)) <= pred(A, x, r)";
by (step_tac (ZF_cs addSIs [predI]) 1);
(*Case analysis on  xaa vs x in r *)
by (forw_inst_tac [("A","A")] well_ord_is_linear 1);
by (linear_case_tac 1);
(*Trivial case: xaa=x*)
by (fast_tac ZF_cs 1);
(*Harder case: <x, xaa>: r*)
by (forward_tac [ord_iso_is_bij RS bij_is_fun RS apply_type] 1  THEN
    REPEAT1 (eresolve_tac [asm_rl, predI, predE] 1));
by (forward_tac [ord_iso_restrict_pred] 1  THEN
    REPEAT1 (eresolve_tac [asm_rl, predI] 1));
by (asm_full_simp_tac
    (ZF_ss addsimps [well_ord_is_trans_on, trans_pred_pred_eq]) 1);
by (fast_tac ZF_cs 1);
qed "domain_ord_iso_map_subset";

(*For the 4-way case analysis in the main result*)
goal Order.thy
  "!!B. [| well_ord(A,r);  well_ord(B,s) |] ==> \
\       domain(ord_iso_map(A,r,B,s)) = A |	\
\       (EX x:A. domain(ord_iso_map(A,r,B,s)) = pred(A,x,r))";
by (forward_tac [well_ord_is_wf] 1);
by (rewrite_goals_tac [wf_on_def, wf_def]);
by (dres_inst_tac [("x", "A-domain(ord_iso_map(A,r,B,s))")] spec 1);
by (step_tac ZF_cs 1);
(*The first case: the domain equals A*)
by (rtac (domain_ord_iso_map RS equalityI) 1);
by (etac (Diff_eq_0_iff RS iffD1) 1);
(*The other case: the domain equals an initial segment*)
by (swap_res_tac [bexI] 1);
by (assume_tac 2);
by (rtac equalityI 1);
(*not ZF_cs below; that would use rules like domainE!*)
by (fast_tac (pair_cs addSEs [predE]) 2);
by (REPEAT (ares_tac [domain_ord_iso_map_subset] 1));
qed "domain_ord_iso_map_cases";

(*As above, by duality*)
goal Order.thy
  "!!B. [| well_ord(A,r);  well_ord(B,s) |] ==>	\
\       range(ord_iso_map(A,r,B,s)) = B |	\
\       (EX y:B. range(ord_iso_map(A,r,B,s))= pred(B,y,s))";
by (resolve_tac [converse_ord_iso_map RS subst] 1);
by (asm_simp_tac
    (ZF_ss addsimps [range_converse, domain_ord_iso_map_cases]) 1);
qed "range_ord_iso_map_cases";

(*Kunen's Theorem 6.3: Fundamental Theorem for Well-Ordered Sets*)
goal Order.thy
  "!!B. [| well_ord(A,r);  well_ord(B,s) |] ==>  	\
\       ord_iso_map(A,r,B,s) : ord_iso(A, r, B, s) |	\
\       (EX x:A. ord_iso_map(A,r,B,s) : ord_iso(pred(A,x,r), r, B, s)) | \
\       (EX y:B. ord_iso_map(A,r,B,s) : ord_iso(A, r, pred(B,y,s), s))";
by (forw_inst_tac [("B","B")] domain_ord_iso_map_cases 1);
by (forw_inst_tac [("B","B")] range_ord_iso_map_cases 2);
by (REPEAT_FIRST (eresolve_tac [asm_rl, disjE, bexE]));
by (ALLGOALS (dresolve_tac [ord_iso_map_ord_iso] THEN' assume_tac THEN' 
	      asm_full_simp_tac (ZF_ss addsimps [bexI])));

by (resolve_tac [wf_on_not_refl RS notE] 1);
by (eresolve_tac [well_ord_is_wf] 1);
by (assume_tac 1);
by (subgoal_tac "<x,y>: ord_iso_map(A,r,B,s)" 1);
by (dresolve_tac [rangeI] 1);
by (asm_full_simp_tac (ZF_ss addsimps [pred_def]) 1);
by (rewrite_goals_tac [ord_iso_map_def]);
by (fast_tac ZF_cs 1);
qed "well_ord_trichotomy";

