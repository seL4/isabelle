(*  Title: 	ZF/OrderArith.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Towards ordinal arithmetic 
*)

(*for deleting an unwanted assumption*)
val thin = prove_goal pure_thy "[| PROP P; PROP Q |] ==> PROP Q"
     (fn prems => [resolve_tac prems 1]);

open OrderArith;


(**** Addition of relations -- disjoint sum ****)

(** Rewrite rules.  Can be used to obtain introduction rules **)

goalw OrderArith.thy [radd_def] 
    "<Inl(a), Inr(b)> : radd(A,r,B,s)  <->  a:A & b:B";
by (fast_tac sum_cs 1);
val radd_Inl_Inr_iff = result();

goalw OrderArith.thy [radd_def] 
    "<Inl(a'), Inl(a)> : radd(A,r,B,s)  <->  <a',a>:r & a':A & a:A";
by (fast_tac sum_cs 1);
val radd_Inl_iff = result();

goalw OrderArith.thy [radd_def] 
    "<Inr(b'), Inr(b)> : radd(A,r,B,s) <->  <b',b>:s & b':B & b:B";
by (fast_tac sum_cs 1);
val radd_Inr_iff = result();

goalw OrderArith.thy [radd_def] 
    "<Inr(b), Inl(a)> : radd(A,r,B,s) <->  False";
by (fast_tac sum_cs 1);
val radd_Inr_Inl_iff = result();

(** Elimination Rule **)

val major::prems = goalw OrderArith.thy [radd_def]
    "[| <p',p> : radd(A,r,B,s);			\
\       !!x y. [| p'=Inl(x); x:A; p=Inr(y); y:B |] ==> Q;	\
\       !!x' x. [| p'=Inl(x'); p=Inl(x); <x',x>: r; x':A; x:A |] ==> Q;	\
\       !!y' y. [| p'=Inr(y'); p=Inr(y); <y',y>: s; y':B; y:B |] ==> Q	\
\    |] ==> Q";
by (cut_facts_tac [major] 1);
(*Split into the three cases*)
by (REPEAT_FIRST
    (eresolve_tac [CollectE, Pair_inject, conjE, exE, SigmaE, disjE]));
(*Apply each premise to correct subgoal; can't just use fast_tac
  because hyp_subst_tac would delete equalities too quickly*)
by (EVERY (map (fn prem => 
		EVERY1 [rtac prem, assume_tac, REPEAT o fast_tac sum_cs])
	   prems));
val raddE = result();

(** Type checking **)

goalw OrderArith.thy [radd_def] "radd(A,r,B,s) <= (A+B) * (A+B)";
by (rtac Collect_subset 1);
val radd_type = result();

val field_radd = standard (radd_type RS field_rel_subset);

(** Linearity **)

val sum_ss = ZF_ss addsimps [Pair_iff, InlI, InrI, Inl_iff, Inr_iff, 
			     Inl_Inr_iff, Inr_Inl_iff];

val radd_ss = sum_ss addsimps [radd_Inl_iff, radd_Inr_iff, 
			       radd_Inl_Inr_iff, radd_Inr_Inl_iff];

goalw OrderArith.thy [linear_def]
    "!!r s. [| linear(A,r);  linear(B,s) |] ==> linear(A+B,radd(A,r,B,s))";
by (REPEAT_FIRST (ares_tac [ballI] ORELSE' etac sumE));
by (ALLGOALS (asm_simp_tac radd_ss));
val linear_radd = result();


(** Well-foundedness **)

goal OrderArith.thy
    "!!r s. [| wf[A](r);  wf[B](s) |] ==> wf[A+B](radd(A,r,B,s))";
by (rtac wf_onI2 1);
by (subgoal_tac "ALL x:A. Inl(x): Ba" 1);
(*Proving the lemma, which is needed twice!*)
by (eres_inst_tac [("P", "y : A + B")] thin 2);
by (rtac ballI 2);
by (eres_inst_tac [("r","r"),("a","x")] wf_on_induct 2 THEN assume_tac 2);
by (etac (bspec RS mp) 2);
by (fast_tac sum_cs 2);
by (best_tac (sum_cs addSEs [raddE]) 2);
(*Returning to main part of proof*)
by (REPEAT_FIRST (eresolve_tac [sumE, ssubst]));
by (best_tac sum_cs 1);
by (eres_inst_tac [("r","s"),("a","ya")] wf_on_induct 1 THEN assume_tac 1);
by (etac (bspec RS mp) 1);
by (fast_tac sum_cs 1);
by (best_tac (sum_cs addSEs [raddE]) 1);
val wf_on_radd = result();

goal OrderArith.thy
     "!!r s. [| wf(r);  wf(s) |] ==> wf(radd(field(r),r,field(s),s))";
by (asm_full_simp_tac (ZF_ss addsimps [wf_iff_wf_on_field]) 1);
by (rtac (field_radd RSN (2, wf_on_subset_A)) 1);
by (REPEAT (ares_tac [wf_on_radd] 1));
val wf_radd = result();

goal OrderArith.thy 
    "!!r s. [| well_ord(A,r);  well_ord(B,s) |] ==> \
\           well_ord(A+B, radd(A,r,B,s))";
by (rtac well_ordI 1);
by (asm_full_simp_tac (ZF_ss addsimps [well_ord_def, wf_on_radd]) 1);
by (asm_full_simp_tac 
    (ZF_ss addsimps [well_ord_def, tot_ord_def, linear_radd]) 1);
val well_ord_radd = result();


(**** Multiplication of relations -- lexicographic product ****)

(** Rewrite rule.  Can be used to obtain introduction rules **)

goalw OrderArith.thy [rmult_def] 
    "!!r s. <<a',b'>, <a,b>> : rmult(A,r,B,s) <-> 	\
\           (<a',a>: r  & a':A & a:A & b': B & b: B) | 	\
\           (<b',b>: s  & a'=a & a:A & b': B & b: B)";
by (fast_tac ZF_cs 1);
val rmult_iff = result();

val major::prems = goal OrderArith.thy
    "[| <<a',b'>, <a,b>> : rmult(A,r,B,s);		\
\       [| <a',a>: r;  a':A;  a:A;  b':B;  b:B |] ==> Q;	\
\       [| <b',b>: s;  a:A;  a'=a;  b':B;  b:B |] ==> Q	\
\    |] ==> Q";
by (rtac (major RS (rmult_iff RS iffD1) RS disjE) 1);
by (DEPTH_SOLVE (eresolve_tac ([asm_rl, conjE] @ prems) 1));
val rmultE = result();

(** Type checking **)

goalw OrderArith.thy [rmult_def] "rmult(A,r,B,s) <= (A*B) * (A*B)";
by (rtac Collect_subset 1);
val rmult_type = result();

val field_rmult = standard (rmult_type RS field_rel_subset);

(** Linearity **)

val [lina,linb] = goal OrderArith.thy
    "[| linear(A,r);  linear(B,s) |] ==> linear(A*B,rmult(A,r,B,s))";
by (rewtac linear_def);    (*Note! the premises are NOT rewritten*)
by (REPEAT_FIRST (ares_tac [ballI] ORELSE' etac SigmaE));
by (asm_simp_tac (ZF_ss addsimps [rmult_iff]) 1);
by (res_inst_tac [("x","xa"), ("y","xb")] (lina RS linearE) 1);
by (res_inst_tac [("x","ya"), ("y","yb")] (linb RS linearE) 4);
by (REPEAT_SOME (fast_tac ZF_cs));
val linear_rmult = result();


(** Well-foundedness **)

goal OrderArith.thy
    "!!r s. [| wf[A](r);  wf[B](s) |] ==> wf[A*B](rmult(A,r,B,s))";
by (rtac wf_onI2 1);
by (etac SigmaE 1);
by (etac ssubst 1);
by (subgoal_tac "ALL b:B. <x,b>: Ba" 1);
by (fast_tac ZF_cs 1);
by (eres_inst_tac [("a","x")] wf_on_induct 1 THEN assume_tac 1);
by (rtac ballI 1);
by (eres_inst_tac [("a","b")] wf_on_induct 1 THEN assume_tac 1);
by (etac (bspec RS mp) 1);
by (fast_tac ZF_cs 1);
by (best_tac (ZF_cs addSEs [rmultE]) 1);
val wf_on_rmult = result();


goal OrderArith.thy
    "!!r s. [| wf(r);  wf(s) |] ==> wf(rmult(field(r),r,field(s),s))";
by (asm_full_simp_tac (ZF_ss addsimps [wf_iff_wf_on_field]) 1);
by (rtac (field_rmult RSN (2, wf_on_subset_A)) 1);
by (REPEAT (ares_tac [wf_on_rmult] 1));
val wf_rmult = result();

goal OrderArith.thy 
    "!!r s. [| well_ord(A,r);  well_ord(B,s) |] ==> \
\           well_ord(A*B, rmult(A,r,B,s))";
by (rtac well_ordI 1);
by (asm_full_simp_tac (ZF_ss addsimps [well_ord_def, wf_on_rmult]) 1);
by (asm_full_simp_tac 
    (ZF_ss addsimps [well_ord_def, tot_ord_def, linear_rmult]) 1);
val well_ord_rmult = result();


(**** Inverse image of a relation ****)

(** Rewrite rule **)

goalw OrderArith.thy [rvimage_def] 
    "<a,b> : rvimage(A,f,r)  <->  <f`a,f`b>: r & a:A & b:A";
by (fast_tac ZF_cs 1);
val rvimage_iff = result();

(** Type checking **)

goalw OrderArith.thy [rvimage_def] "rvimage(A,f,r) <= A*A";
by (rtac Collect_subset 1);
val rvimage_type = result();

val field_rvimage = standard (rvimage_type RS field_rel_subset);


(** Linearity **)

val [finj,lin] = goalw OrderArith.thy [inj_def]
    "[| f: inj(A,B);  linear(B,r) |] ==> linear(A,rvimage(A,f,r))";
by (rewtac linear_def);    (*Note! the premises are NOT rewritten*)
by (REPEAT_FIRST (ares_tac [ballI]));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff]) 1);
by (cut_facts_tac [finj] 1);
by (res_inst_tac [("x","f`x"), ("y","f`y")] (lin RS linearE) 1);
by (REPEAT_SOME (fast_tac (ZF_cs addSIs [apply_type])));
val linear_rvimage = result();


(** Well-foundedness **)

goal OrderArith.thy
    "!!r. [| f: A->B;  wf[B](r) |] ==> wf[A](rvimage(A,f,r))";
by (rtac wf_onI2 1);
by (subgoal_tac "ALL z:A. f`z=f`y --> z: Ba" 1);
by (fast_tac ZF_cs 1);
by (eres_inst_tac [("a","f`y")] wf_on_induct 1);
by (fast_tac (ZF_cs addSIs [apply_type]) 1);
by (best_tac (ZF_cs addSIs [apply_type] addSDs [rvimage_iff RS iffD1]) 1);
val wf_on_rvimage = result();

goal OrderArith.thy 
    "!!r. [| f: inj(A,B);  well_ord(B,r) |] ==> well_ord(A, rvimage(A,f,r))";
by (rtac well_ordI 1);
by (rewrite_goals_tac [well_ord_def, tot_ord_def]);
by (fast_tac (ZF_cs addSIs [wf_on_rvimage, inj_is_fun]) 1);
by (fast_tac (ZF_cs addSIs [linear_rvimage]) 1);
val well_ord_rvimage = result();
