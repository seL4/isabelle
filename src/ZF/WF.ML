(*  Title: 	ZF/wf.ML
    ID:         $Id$
    Author: 	Tobias Nipkow and Lawrence C Paulson
    Copyright   1992  University of Cambridge

For wf.thy.  Well-founded Recursion

Derived first for transitive relations, and finally for arbitrary WF relations
via wf_trancl and trans_trancl.

It is difficult to derive this general case directly, using r^+ instead of
r.  In is_recfun, the two occurrences of the relation must have the same
form.  Inserting r^+ in the_recfun or wftrec yields a recursion rule with
r^+ -`` {a} instead of r-``{a}.  This recursion rule is stronger in
principle, but harder to use, especially to prove wfrec_eclose_eq in
epsilon.ML.  Expanding out the definition of wftrec in wfrec would yield
a mess.
*)

open WF;


(*** Well-founded relations ***)

(*Are these two theorems at all useful??*)

(*If every subset of field(r) possesses an r-minimal element then wf(r).
  Seems impossible to prove this for domain(r) or range(r) instead...
  Consider in particular finite wf relations!*)
val [prem1,prem2] = goalw WF.thy [wf_def]
    "[| field(r)<=A;  \
\       !!Z u. [| Z<=A;  u:Z;  ALL x:Z. EX y:Z. <y,x>:r |] ==> False |] \
\    ==>  wf(r)";
by (rtac (equals0I RS disjCI RS allI) 1);
by (rtac prem2 1);
by (res_inst_tac [ ("B1", "Z") ] (prem1 RS (Int_lower1 RS subset_trans)) 1);
by (fast_tac ZF_cs 1);
by (fast_tac ZF_cs 1);
val wfI = result();

(*If r allows well-founded induction then wf(r)*)
val [prem1,prem2] = goal WF.thy
    "[| field(r)<=A;  \
\       !!B. ALL x:A. (ALL y. <y,x>: r --> y:B) --> x:B ==> A<=B |]  \
\    ==>  wf(r)";
by (rtac (prem1 RS wfI) 1);
by (res_inst_tac [ ("B", "A-Z") ] (prem2 RS subsetCE) 1);
by (fast_tac ZF_cs 3);
by (fast_tac ZF_cs 2);
by (fast_tac ZF_cs 1);
val wfI2 = result();


(** Well-founded Induction **)

(*Consider the least z in domain(r) Un {a} such that P(z) does not hold...*)
val major::prems = goalw WF.thy [wf_def]
    "[| wf(r);          \
\       !!x.[| ALL y. <y,x>: r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (res_inst_tac [ ("x", "{z:domain(r) Un {a}. ~P(z)}") ]  (major RS allE) 1);
by (etac disjE 1);
by (rtac classical 1);
by (etac equals0D 1);
by (etac (singletonI RS UnI2 RS CollectI) 1);
by (etac bexE 1);
by (etac CollectE 1);
by (etac swap 1);
by (resolve_tac prems 1);
by (fast_tac ZF_cs 1);
val wf_induct = result();

(*Perform induction on i, then prove the wf(r) subgoal using prems. *)
fun wf_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_induct i,
	   rename_last_tac a ["1"] (i+1),
	   ares_tac prems i];

(*The form of this rule is designed to match wfI2*)
val wfr::amem::prems = goal WF.thy
    "[| wf(r);  a:A;  field(r)<=A;  \
\       !!x.[| x: A;  ALL y. <y,x>: r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (rtac (amem RS rev_mp) 1);
by (wf_ind_tac "a" [wfr] 1);
by (rtac impI 1);
by (eresolve_tac prems 1);
by (fast_tac (ZF_cs addIs (prems RL [subsetD])) 1);
val wf_induct2 = result();

val prems = goal WF.thy "[| wf(r);  <a,x>:r;  <x,a>:r |] ==> False";
by (subgoal_tac "ALL x. <a,x>:r --> <x,a>:r --> False" 1);
by (wf_ind_tac "a" prems 2);
by (fast_tac ZF_cs 2);
by (fast_tac (FOL_cs addIs prems) 1);
val wf_anti_sym = result();

(*transitive closure of a WF relation is WF!*)
val [prem] = goal WF.thy "wf(r) ==> wf(r^+)";
by (rtac (trancl_type RS field_rel_subset RS wfI2) 1);
by (rtac subsetI 1);
(*must retain the universal formula for later use!*)
by (rtac (bspec RS mp) 1 THEN assume_tac 1 THEN assume_tac 1);
by (eres_inst_tac [("a","x")] (prem RS wf_induct2) 1);
by (rtac subset_refl 1);
by (rtac (impI RS allI) 1);
by (etac tranclE 1);
by (etac (bspec RS mp) 1);
by (etac fieldI1 1);
by (fast_tac ZF_cs 1);
by (fast_tac ZF_cs 1);
val wf_trancl = result();

(** r-``{a} is the set of everything under a in r **)

val underI = standard (vimage_singleton_iff RS iffD2);
val underD = standard (vimage_singleton_iff RS iffD1);

(** is_recfun **)

val [major] = goalw WF.thy [is_recfun_def]
    "is_recfun(r,a,H,f) ==> f: r-``{a} -> range(f)";
by (rtac (major RS ssubst) 1);
by (rtac (lamI RS rangeI RS lam_type) 1);
by (assume_tac 1);
val is_recfun_type = result();

val [isrec,rel] = goalw WF.thy [is_recfun_def]
    "[| is_recfun(r,a,H,f); <x,a>:r |] ==> f`x = H(x, restrict(f,r-``{x}))";
by (res_inst_tac [("P", "%x.?t(x) = ?u::i")] (isrec RS ssubst) 1);
by (rtac (rel RS underI RS beta) 1);
val apply_recfun = result();

(*eresolve_tac transD solves <a,b>:r using transitivity AT MOST ONCE
  spec RS mp  instantiates induction hypotheses*)
fun indhyp_tac hyps =
    resolve_tac (TrueI::refl::hyps) ORELSE' 
    (cut_facts_tac hyps THEN'
       DEPTH_SOLVE_1 o (ares_tac [TrueI, ballI] ORELSE'
		        eresolve_tac [underD, transD, spec RS mp]));

(*** NOTE! some simplifications need a different solver!! ***)
val wf_super_ss = ZF_ss setsolver indhyp_tac;

val prems = goalw WF.thy [is_recfun_def]
    "[| wf(r);  trans(r);  is_recfun(r,a,H,f);  is_recfun(r,b,H,g) |] ==> \
\    <x,a>:r --> <x,b>:r --> f`x=g`x";
by (cut_facts_tac prems 1);
by (wf_ind_tac "x" prems 1);
by (REPEAT (rtac impI 1 ORELSE etac ssubst 1));
by (rewtac restrict_def);
by (asm_simp_tac (wf_super_ss addsimps [vimage_singleton_iff]) 1);
val is_recfun_equal_lemma = result();
val is_recfun_equal = standard (is_recfun_equal_lemma RS mp RS mp);

val prems as [wfr,transr,recf,recg,_] = goal WF.thy
    "[| wf(r);  trans(r);       \
\       is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  <b,a>:r |] ==> \
\    restrict(f, r-``{b}) = g";
by (cut_facts_tac prems 1);
by (rtac (consI1 RS restrict_type RS fun_extension) 1);
by (etac is_recfun_type 1);
by (ALLGOALS
    (asm_simp_tac (wf_super_ss addsimps
		   [ [wfr,transr,recf,recg] MRS is_recfun_equal ])));
val is_recfun_cut = result();

(*** Main Existence Lemma ***)

val prems = goal WF.thy
    "[| wf(r); trans(r); is_recfun(r,a,H,f); is_recfun(r,a,H,g) |]  ==>  f=g";
by (cut_facts_tac prems 1);
by (rtac fun_extension 1);
by (REPEAT (ares_tac [is_recfun_equal] 1
     ORELSE eresolve_tac [is_recfun_type,underD] 1));
val is_recfun_functional = result();

(*If some f satisfies is_recfun(r,a,H,-) then so does the_recfun(r,a,H) *)
val prems = goalw WF.thy [the_recfun_def]
    "[| is_recfun(r,a,H,f);  wf(r);  trans(r) |]  \
\    ==> is_recfun(r, a, H, the_recfun(r,a,H))";
by (rtac (ex1I RS theI) 1);
by (REPEAT (ares_tac (prems@[is_recfun_functional]) 1));
val is_the_recfun = result();

val prems = goal WF.thy
    "[| wf(r);  trans(r) |] ==> is_recfun(r, a, H, the_recfun(r,a,H))";
by (cut_facts_tac prems 1);
by (wf_ind_tac "a" prems 1);
by (res_inst_tac [("f", "lam y: r-``{a1}. wftrec(r,y,H)")] is_the_recfun 1);
by (REPEAT (assume_tac 2));
by (rewrite_goals_tac [is_recfun_def, wftrec_def]);
(*Applying the substitution: must keep the quantified assumption!!*)
by (REPEAT (dtac underD 1 ORELSE resolve_tac [refl, lam_cong] 1));
by (fold_tac [is_recfun_def]);
by (rtac (consI1 RS restrict_type RSN (2,fun_extension) RS subst_context) 1);
by (rtac is_recfun_type 1);
by (ALLGOALS
    (asm_simp_tac
     (wf_super_ss addsimps [underI RS beta, apply_recfun, is_recfun_cut])));
val unfold_the_recfun = result();


(*** Unfolding wftrec ***)

val prems = goal WF.thy
    "[| wf(r);  trans(r);  <b,a>:r |] ==> \
\    restrict(the_recfun(r,a,H), r-``{b}) = the_recfun(r,b,H)";
by (REPEAT (ares_tac (prems @ [is_recfun_cut, unfold_the_recfun]) 1));
val the_recfun_cut = result();

(*NOT SUITABLE FOR REWRITING since it is recursive!*)
goalw WF.thy [wftrec_def]
    "!!r. [| wf(r);  trans(r) |] ==> \
\         wftrec(r,a,H) = H(a, lam x: r-``{a}. wftrec(r,x,H))";
by (rtac (rewrite_rule [is_recfun_def] unfold_the_recfun RS ssubst) 1);
by (ALLGOALS (asm_simp_tac
	(ZF_ss addsimps [vimage_singleton_iff RS iff_sym, the_recfun_cut])));
val wftrec = result();

(** Removal of the premise trans(r) **)

(*NOT SUITABLE FOR REWRITING since it is recursive!*)
val [wfr] = goalw WF.thy [wfrec_def]
    "wf(r) ==> wfrec(r,a,H) = H(a, lam x:r-``{a}. wfrec(r,x,H))";
by (rtac (wfr RS wf_trancl RS wftrec RS ssubst) 1);
by (rtac trans_trancl 1);
by (rtac (vimage_pair_mono RS restrict_lam_eq RS subst_context) 1);
by (etac r_into_trancl 1);
by (rtac subset_refl 1);
val wfrec = result();

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
val rew::prems = goal WF.thy
    "[| !!x. h(x)==wfrec(r,x,H);  wf(r) |] ==> \
\    h(a) = H(a, lam x: r-``{a}. h(x))";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[wfrec]) 1));
val def_wfrec = result();

val prems = goal WF.thy
    "[| wf(r);  a:A;  field(r)<=A;  \
\       !!x u. [| x: A;  u: Pi(r-``{x}, B) |] ==> H(x,u) : B(x)   \
\    |] ==> wfrec(r,a,H) : B(a)";
by (res_inst_tac [("a","a")] wf_induct2 1);
by (rtac (wfrec RS ssubst) 4);
by (REPEAT (ares_tac (prems@[lam_type]) 1
     ORELSE eresolve_tac [spec RS mp, underD] 1));
val wfrec_type = result();
