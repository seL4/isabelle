(*  Title:      ZF/wf.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Lawrence C Paulson
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

(** Equivalences between wf and wf_on **)

goalw WF.thy [wf_def, wf_on_def] "!!A r. wf(r) ==> wf[A](r)";
by (fast_tac ZF_cs 1);
qed "wf_imp_wf_on";

goalw WF.thy [wf_def, wf_on_def] "!!r. wf[field(r)](r) ==> wf(r)";
by (fast_tac ZF_cs 1);
qed "wf_on_field_imp_wf";

goal WF.thy "wf(r) <-> wf[field(r)](r)";
by (fast_tac (ZF_cs addSEs [wf_imp_wf_on, wf_on_field_imp_wf]) 1);
qed "wf_iff_wf_on_field";

goalw WF.thy [wf_on_def, wf_def] "!!A B r. [| wf[A](r);  B<=A |] ==> wf[B](r)";
by (fast_tac ZF_cs 1);
qed "wf_on_subset_A";

goalw WF.thy [wf_on_def, wf_def] "!!A r s. [| wf[A](r);  s<=r |] ==> wf[A](s)";
by (fast_tac ZF_cs 1);
qed "wf_on_subset_r";

(** Introduction rules for wf_on **)

(*If every non-empty subset of A has an r-minimal element then wf[A](r).*)
val [prem] = goalw WF.thy [wf_on_def, wf_def]
    "[| !!Z u. [| Z<=A;  u:Z;  ALL x:Z. EX y:Z. <y,x>:r |] ==> False |] \
\    ==>  wf[A](r)";
by (rtac (equals0I RS disjCI RS allI) 1);
by (res_inst_tac [ ("Z", "Z") ] prem 1);
by (ALLGOALS (fast_tac ZF_cs));
qed "wf_onI";

(*If r allows well-founded induction over A then wf[A](r)
  Premise is equivalent to 
  !!B. ALL x:A. (ALL y. <y,x>: r --> y:B) --> x:B ==> A<=B  *)
val [prem] = goal WF.thy
    "[| !!y B. [| ALL x:A. (ALL y:A. <y,x>:r --> y:B) --> x:B;   y:A  \
\              |] ==> y:B |] \
\    ==>  wf[A](r)";
by (rtac wf_onI 1);
by (res_inst_tac [ ("c", "u") ] (prem RS DiffE) 1);
by (contr_tac 3);
by (fast_tac ZF_cs 2);
by (fast_tac ZF_cs 1);
qed "wf_onI2";


(** Well-founded Induction **)

(*Consider the least z in domain(r) Un {a} such that P(z) does not hold...*)
val [major,minor] = goalw WF.thy [wf_def]
    "[| wf(r);          \
\       !!x.[| ALL y. <y,x>: r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (res_inst_tac [ ("x", "{z:domain(r) Un {a}. ~P(z)}") ]  (major RS allE) 1);
by (etac disjE 1);
by (fast_tac (ZF_cs addEs [equalityE]) 1);
by (asm_full_simp_tac (ZF_ss addsimps [domainI]) 1);
by (etac bexE 1);
by (dtac minor 1);
by (fast_tac ZF_cs 1);
qed "wf_induct";

(*Perform induction on i, then prove the wf(r) subgoal using prems. *)
fun wf_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_induct i,
           rename_last_tac a ["1"] (i+1),
           ares_tac prems i];

(*The form of this rule is designed to match wfI*)
val wfr::amem::prems = goal WF.thy
    "[| wf(r);  a:A;  field(r)<=A;  \
\       !!x.[| x: A;  ALL y. <y,x>: r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (rtac (amem RS rev_mp) 1);
by (wf_ind_tac "a" [wfr] 1);
by (rtac impI 1);
by (eresolve_tac prems 1);
by (fast_tac (ZF_cs addIs (prems RL [subsetD])) 1);
qed "wf_induct2";

goal ZF.thy "!!r A. field(r Int A*A) <= A";
by (fast_tac ZF_cs 1);
qed "field_Int_square";

val wfr::amem::prems = goalw WF.thy [wf_on_def]
    "[| wf[A](r);  a:A;                                         \
\       !!x.[| x: A;  ALL y:A. <y,x>: r --> P(y) |] ==> P(x)    \
\    |]  ==>  P(a)";
by (rtac ([wfr, amem, field_Int_square] MRS wf_induct2) 1);
by (REPEAT (ares_tac prems 1));
by (fast_tac ZF_cs 1);
qed "wf_on_induct";

fun wf_on_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_on_induct i,
           rename_last_tac a ["1"] (i+2),
           REPEAT (ares_tac prems i)];

(*If r allows well-founded induction then wf(r)*)
val [subs,indhyp] = goal WF.thy
    "[| field(r)<=A;  \
\       !!y B. [| ALL x:A. (ALL y:A. <y,x>:r --> y:B) --> x:B;   y:A  \
\              |] ==> y:B |] \
\    ==>  wf(r)";
by (rtac ([wf_onI2, subs] MRS (wf_on_subset_A RS wf_on_field_imp_wf)) 1);
by (REPEAT (ares_tac [indhyp] 1));
qed "wfI";


(*** Properties of well-founded relations ***)

goal WF.thy "!!r. wf(r) ==> <a,a> ~: r";
by (wf_ind_tac "a" [] 1);
by (fast_tac ZF_cs 1);
qed "wf_not_refl";

goal WF.thy "!!r. [| wf(r);  <a,x>:r;  <x,a>:r |] ==> P";
by (subgoal_tac "ALL x. <a,x>:r --> <x,a>:r --> P" 1);
by (wf_ind_tac "a" [] 2);
by (fast_tac ZF_cs 2);
by (fast_tac FOL_cs 1);
qed "wf_asym";

goal WF.thy "!!r. [| wf[A](r); a: A |] ==> <a,a> ~: r";
by (wf_on_ind_tac "a" [] 1);
by (fast_tac ZF_cs 1);
qed "wf_on_not_refl";

goal WF.thy "!!r. [| wf[A](r);  <a,b>:r;  <b,a>:r;  a:A;  b:A |] ==> P";
by (subgoal_tac "ALL y:A. <a,y>:r --> <y,a>:r --> P" 1);
by (wf_on_ind_tac "a" [] 2);
by (fast_tac ZF_cs 2);
by (fast_tac ZF_cs 1);
qed "wf_on_asym";

(*Needed to prove well_ordI.  Could also reason that wf[A](r) means
  wf(r Int A*A);  thus wf( (r Int A*A)^+ ) and use wf_not_refl *)
goal WF.thy
    "!!r. [| wf[A](r); <a,b>:r; <b,c>:r; <c,a>:r; a:A; b:A; c:A |] ==> P";
by (subgoal_tac
    "ALL y:A. ALL z:A. <a,y>:r --> <y,z>:r --> <z,a>:r --> P" 1);
by (wf_on_ind_tac "a" [] 2);
by (fast_tac ZF_cs 2);
by (fast_tac ZF_cs 1);
qed "wf_on_chain3";


(*retains the universal formula for later use!*)
val bchain_tac = EVERY' [rtac (bspec RS mp), assume_tac, assume_tac ];

(*transitive closure of a WF relation is WF provided A is downwards closed*)
val [wfr,subs] = goal WF.thy
    "[| wf[A](r);  r-``A <= A |] ==> wf[A](r^+)";
by (rtac wf_onI2 1);
by (bchain_tac 1);
by (eres_inst_tac [("a","y")] (wfr RS wf_on_induct) 1);
by (rtac (impI RS ballI) 1);
by (etac tranclE 1);
by (etac (bspec RS mp) 1 THEN assume_tac 1);
by (fast_tac ZF_cs 1);
by (cut_facts_tac [subs] 1);
(*astar_tac is slightly faster*)
by (best_tac ZF_cs 1);
qed "wf_on_trancl";

goal WF.thy "!!r. wf(r) ==> wf(r^+)";
by (asm_full_simp_tac (ZF_ss addsimps [wf_iff_wf_on_field]) 1);
by (rtac (trancl_type RS field_rel_subset RSN (2, wf_on_subset_A)) 1);
by (etac wf_on_trancl 1);
by (fast_tac ZF_cs 1);
qed "wf_trancl";



(** r-``{a} is the set of everything under a in r **)

bind_thm ("underI", (vimage_singleton_iff RS iffD2));
bind_thm ("underD", (vimage_singleton_iff RS iffD1));

(** is_recfun **)

val [major] = goalw WF.thy [is_recfun_def]
    "is_recfun(r,a,H,f) ==> f: r-``{a} -> range(f)";
by (stac major 1);
by (rtac (lamI RS rangeI RS lam_type) 1);
by (assume_tac 1);
qed "is_recfun_type";

val [isrec,rel] = goalw WF.thy [is_recfun_def]
    "[| is_recfun(r,a,H,f); <x,a>:r |] ==> f`x = H(x, restrict(f,r-``{x}))";
by (res_inst_tac [("P", "%x.?t(x) = (?u::i)")] (isrec RS ssubst) 1);
by (rtac (rel RS underI RS beta) 1);
qed "apply_recfun";

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
qed "is_recfun_equal_lemma";
bind_thm ("is_recfun_equal", (is_recfun_equal_lemma RS mp RS mp));

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
qed "is_recfun_cut";

(*** Main Existence Lemma ***)

val prems = goal WF.thy
    "[| wf(r); trans(r); is_recfun(r,a,H,f); is_recfun(r,a,H,g) |]  ==>  f=g";
by (cut_facts_tac prems 1);
by (rtac fun_extension 1);
by (REPEAT (ares_tac [is_recfun_equal] 1
     ORELSE eresolve_tac [is_recfun_type,underD] 1));
qed "is_recfun_functional";

(*If some f satisfies is_recfun(r,a,H,-) then so does the_recfun(r,a,H) *)
val prems = goalw WF.thy [the_recfun_def]
    "[| is_recfun(r,a,H,f);  wf(r);  trans(r) |]  \
\    ==> is_recfun(r, a, H, the_recfun(r,a,H))";
by (rtac (ex1I RS theI) 1);
by (REPEAT (ares_tac (prems@[is_recfun_functional]) 1));
qed "is_the_recfun";

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
qed "unfold_the_recfun";


(*** Unfolding wftrec ***)

val prems = goal WF.thy
    "[| wf(r);  trans(r);  <b,a>:r |] ==> \
\    restrict(the_recfun(r,a,H), r-``{b}) = the_recfun(r,b,H)";
by (REPEAT (ares_tac (prems @ [is_recfun_cut, unfold_the_recfun]) 1));
qed "the_recfun_cut";

(*NOT SUITABLE FOR REWRITING since it is recursive!*)
goalw WF.thy [wftrec_def]
    "!!r. [| wf(r);  trans(r) |] ==> \
\         wftrec(r,a,H) = H(a, lam x: r-``{a}. wftrec(r,x,H))";
by (stac (rewrite_rule [is_recfun_def] unfold_the_recfun) 1);
by (ALLGOALS (asm_simp_tac
        (ZF_ss addsimps [vimage_singleton_iff RS iff_sym, the_recfun_cut])));
qed "wftrec";

(** Removal of the premise trans(r) **)

(*NOT SUITABLE FOR REWRITING since it is recursive!*)
val [wfr] = goalw WF.thy [wfrec_def]
    "wf(r) ==> wfrec(r,a,H) = H(a, lam x:r-``{a}. wfrec(r,x,H))";
by (stac (wfr RS wf_trancl RS wftrec) 1);
by (rtac trans_trancl 1);
by (rtac (vimage_pair_mono RS restrict_lam_eq RS subst_context) 1);
by (etac r_into_trancl 1);
by (rtac subset_refl 1);
qed "wfrec";

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
val rew::prems = goal WF.thy
    "[| !!x. h(x)==wfrec(r,x,H);  wf(r) |] ==> \
\    h(a) = H(a, lam x: r-``{a}. h(x))";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[wfrec]) 1));
qed "def_wfrec";

val prems = goal WF.thy
    "[| wf(r);  a:A;  field(r)<=A;  \
\       !!x u. [| x: A;  u: Pi(r-``{x}, B) |] ==> H(x,u) : B(x)   \
\    |] ==> wfrec(r,a,H) : B(a)";
by (res_inst_tac [("a","a")] wf_induct2 1);
by (stac wfrec 4);
by (REPEAT (ares_tac (prems@[lam_type]) 1
     ORELSE eresolve_tac [spec RS mp, underD] 1));
qed "wfrec_type";


goalw WF.thy [wf_on_def, wfrec_on_def]
 "!!A r. [| wf[A](r);  a: A |] ==> \
\        wfrec[A](r,a,H) = H(a, lam x: (r-``{a}) Int A. wfrec[A](r,x,H))";
by (etac (wfrec RS trans) 1);
by (asm_simp_tac (ZF_ss addsimps [vimage_Int_square, cons_subset_iff]) 1);
qed "wfrec_on";

