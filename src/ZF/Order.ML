(*  Title: 	ZF/Order.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

For Order.thy.  Orders in Zermelo-Fraenkel Set Theory 
*)


open Order;

val bij_apply_cs = ZF_cs addSEs [bij_converse_bij]
                         addIs  [bij_is_fun, apply_type];

val bij_inverse_ss = 
    ZF_ss addsimps [bij_is_fun RS apply_type,
		    bij_converse_bij RS bij_is_fun RS apply_type,
		    left_inverse_bij, right_inverse_bij];

(** Basic properties of the definitions **)

(*needed????*)
goalw Order.thy [part_ord_def, irrefl_def, trans_on_def, asym_def]
    "!!r. part_ord(A,r) ==> asym(r Int A*A)";
by (fast_tac ZF_cs 1);
qed "part_ord_Imp_asym";

(** Subset properties for the various forms of relation **)


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


(** Order-isomorphisms **)

goalw Order.thy [ord_iso_def] 
    "!!f. f: ord_iso(A,r,B,s) ==> f: bij(A,B)";
by (etac CollectD1 1);
qed "ord_iso_is_bij";

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
			REPEAT_SOME assume_tac]);

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
    "!!r. [| well_ord(A,r);  x:A |] ==> \
\         ALL f. f ~: ord_iso(A, r, pred(A,x,r), r)";
by (safe_tac ZF_cs);
by (metacut_tac not_well_ord_iso_pred_lemma 1);
by (REPEAT_SOME assume_tac);
(*Now we know f`x = x*)
by (EVERY1 [dtac (ord_iso_is_bij RS bij_is_fun RS apply_type),
	     assume_tac]);
(*Now we know f`x : pred(A,x,r) *)
by (asm_full_simp_tac (ZF_ss addsimps [well_ord_def, pred_def]) 1);
by (fast_tac (ZF_cs addSEs [wf_on_not_refl RS notE]) 1);
qed "not_well_ord_iso_pred";


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
    "!!r. [| well_ord(A,r);  well_ord(B,s);  \
\            f: ord_iso(A,r, B,s);  g: ord_iso(A,r, B,s) |] ==> f = g";
by (rtac fun_extension 1);
by (etac (ord_iso_is_bij RS bij_is_fun) 1);
by (etac (ord_iso_is_bij RS bij_is_fun) 1);
by (rtac well_ord_iso_unique_lemma 1);
by (REPEAT_SOME assume_tac);
qed "well_ord_iso_unique";


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

(*** Derived rules for pred(A,x,r) ***)

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

goalw Order.thy [pred_def] "y : pred(A,x,r) <-> <y,x>:r & y:A";
by (fast_tac ZF_cs 1);
qed "pred_iff";

goalw Order.thy [pred_def]
    "pred(pred(A,x,r), y, r) = pred(A,x,r) Int pred(A,y,r)";
by (fast_tac eq_cs 1);
qed "pred_pred_eq";
