(*  Title:      HOL/WF.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1992  University of Cambridge

For WF.thy.  Well-founded Recursion
*)

open WF;

val H_cong = read_instantiate [("f","H")] (standard(refl RS cong RS cong));
val H_cong1 = refl RS H_cong;

(*Restriction to domain A.  If r is well-founded over A then wf(r)*)
val [prem1,prem2] = goalw WF.thy [wf_def]
 "[| r <= Sigma A (%u.A);  \
\    !!x P. [| ! x. (! y. (y,x) : r --> P(y)) --> P(x);  x:A |] ==> P(x) |]  \
\ ==>  wf(r)";
by (strip_tac 1);
by (rtac allE 1);
by (assume_tac 1);
by (best_tac (HOL_cs addSEs [prem1 RS subsetD RS SigmaE2] addIs [prem2]) 1);
qed "wfI";

val major::prems = goalw WF.thy [wf_def]
    "[| wf(r);          \
\       !!x.[| ! y. (y,x): r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (rtac (major RS spec RS mp RS spec) 1);
by (fast_tac (HOL_cs addEs prems) 1);
qed "wf_induct";

(*Perform induction on i, then prove the wf(r) subgoal using prems. *)
fun wf_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_induct i,
           rename_last_tac a ["1"] (i+1),
           ares_tac prems i];

val prems = goal WF.thy "[| wf(r);  (a,x):r;  (x,a):r |] ==> P";
by (subgoal_tac "! x. (a,x):r --> (x,a):r --> P" 1);
by (fast_tac (HOL_cs addIs prems) 1);
by (wf_ind_tac "a" prems 1);
by (fast_tac set_cs 1);
qed "wf_asym";

val prems = goal WF.thy "[| wf(r);  (a,a): r |] ==> P";
by (rtac wf_asym 1);
by (REPEAT (resolve_tac prems 1));
qed "wf_anti_refl";

(*transitive closure of a WF relation is WF!*)
val [prem] = goal WF.thy "wf(r) ==> wf(r^+)";
by (rewtac wf_def);
by (strip_tac 1);
(*must retain the universal formula for later use!*)
by (rtac allE 1 THEN assume_tac 1);
by (etac mp 1);
by (res_inst_tac [("a","x")] (prem RS wf_induct) 1);
by (rtac (impI RS allI) 1);
by (etac tranclE 1);
by (fast_tac HOL_cs 1);
by (fast_tac HOL_cs 1);
qed "wf_trancl";


(** cut **)

(*This rewrite rule works upon formulae; thus it requires explicit use of
  H_cong to expose the equality*)
goalw WF.thy [cut_def]
    "(cut f r x = cut g r x) = (!y. (y,x):r --> f(y)=g(y))";
by(simp_tac (!simpset addsimps [expand_fun_eq]
                        setloop (split_tac [expand_if])) 1);
qed "cut_cut_eq";

goalw WF.thy [cut_def] "!!x. (x,a):r ==> (cut f r a)(x) = f(x)";
by(Asm_simp_tac 1);
qed "cut_apply";


(*** is_recfun ***)

goalw WF.thy [is_recfun_def,cut_def]
    "!!f. [| is_recfun r a H f;  ~(b,a):r |] ==> f(b) = (@z.True)";
by (etac ssubst 1);
by(Asm_simp_tac 1);
qed "is_recfun_undef";

(*eresolve_tac transD solves (a,b):r using transitivity AT MOST ONCE
  mp amd allE  instantiate induction hypotheses*)
fun indhyp_tac hyps =
    ares_tac (TrueI::hyps) ORELSE' 
    (cut_facts_tac hyps THEN'
       DEPTH_SOLVE_1 o (ares_tac [TrueI] ORELSE'
                        eresolve_tac [transD, mp, allE]));

(*** NOTE! some simplifications need a different finish_tac!! ***)
fun indhyp_tac hyps =
    resolve_tac (TrueI::refl::hyps) ORELSE' 
    (cut_facts_tac hyps THEN'
       DEPTH_SOLVE_1 o (ares_tac [TrueI] ORELSE'
                        eresolve_tac [transD, mp, allE]));
val wf_super_ss = !simpset setsolver indhyp_tac;

val prems = goalw WF.thy [is_recfun_def,cut_def]
    "[| wf(r);  trans(r);  is_recfun r a H f;  is_recfun r b H g |] ==> \
    \ (x,a):r --> (x,b):r --> f(x)=g(x)";
by (cut_facts_tac prems 1);
by (etac wf_induct 1);
by (REPEAT (rtac impI 1 ORELSE etac ssubst 1));
by (asm_simp_tac (wf_super_ss addcongs [if_cong]) 1);
qed "is_recfun_equal_lemma";
bind_thm ("is_recfun_equal", (is_recfun_equal_lemma RS mp RS mp));


val prems as [wfr,transr,recfa,recgb,_] = goalw WF.thy [cut_def]
    "[| wf(r);  trans(r); \
\       is_recfun r a H f;  is_recfun r b H g;  (b,a):r |] ==> \
\    cut f r b = g";
val gundef = recgb RS is_recfun_undef
and fisg   = recgb RS (recfa RS (transr RS (wfr RS is_recfun_equal)));
by (cut_facts_tac prems 1);
by (rtac ext 1);
by (asm_simp_tac (wf_super_ss addsimps [gundef,fisg]
                              setloop (split_tac [expand_if])) 1);
qed "is_recfun_cut";

(*** Main Existence Lemma -- Basic Properties of the_recfun ***)

val prems = goalw WF.thy [the_recfun_def]
    "is_recfun r a H f ==> is_recfun r a H (the_recfun r a H)";
by (res_inst_tac [("P", "is_recfun r a H")] selectI 1);
by (resolve_tac prems 1);
qed "is_the_recfun";

val prems = goal WF.thy
    "[| wf(r);  trans(r) |] ==> is_recfun r a H (the_recfun r a H)";
by (cut_facts_tac prems 1);
by (wf_ind_tac "a" prems 1);
by (res_inst_tac [("f", "cut (%y. wftrec r y H) r a1")] is_the_recfun 1);
by (rewrite_goals_tac [is_recfun_def, wftrec_def]);
by (rtac (cut_cut_eq RS ssubst) 1);
(*Applying the substitution: must keep the quantified assumption!!*)
by (EVERY1 [strip_tac, rtac H_cong1, rtac allE, atac,
            etac (mp RS ssubst), atac]);
by (fold_tac [is_recfun_def]);
by (asm_simp_tac (wf_super_ss addsimps[cut_apply,is_recfun_cut,cut_cut_eq]) 1);
qed "unfold_the_recfun";


(*Beware incompleteness of unification!*)
val prems = goal WF.thy
    "[| wf(r);  trans(r);  (c,a):r;  (c,b):r |] \
\    ==> the_recfun r a H c = the_recfun r b H c";
by (DEPTH_SOLVE (ares_tac (prems@[is_recfun_equal,unfold_the_recfun]) 1));
qed "the_recfun_equal";

val prems = goal WF.thy
    "[| wf(r); trans(r); (b,a):r |] \
\    ==> cut (the_recfun r a H) r b = the_recfun r b H";
by (REPEAT (ares_tac (prems@[is_recfun_cut,unfold_the_recfun]) 1));
qed "the_recfun_cut";

(*** Unfolding wftrec ***)

goalw WF.thy [wftrec_def]
    "!!r. [| wf(r);  trans(r) |] ==> \
\    wftrec r a H = H a (cut (%x.wftrec r x H) r a)";
by (EVERY1 [stac (rewrite_rule [is_recfun_def] unfold_the_recfun),
            REPEAT o atac, rtac H_cong1]);
by (asm_simp_tac (!simpset addsimps [cut_cut_eq,the_recfun_cut]) 1);
qed "wftrec";

(*Unused but perhaps interesting*)
val prems = goal WF.thy
    "[| wf(r);  trans(r);  !!f x. H x (cut f r x) = H x f |] ==> \
\               wftrec r a H = H a (%x.wftrec r x H)";
by (rtac (wftrec RS trans) 1);
by (REPEAT (resolve_tac prems 1));
qed "wftrec2";

(** Removal of the premise trans(r) **)

goalw WF.thy [wfrec_def]
    "!!r. wf(r) ==> wfrec r a H = H a (cut (%x.wfrec r x H) r a)";
by (etac (wf_trancl RS wftrec RS ssubst) 1);
by (rtac trans_trancl 1);
by (rtac (refl RS H_cong) 1);    (*expose the equality of cuts*)
by (simp_tac (!simpset addsimps [cut_cut_eq, cut_apply, r_into_trancl]) 1);
qed "wfrec";

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
val rew::prems = goal WF.thy
    "[| !!x. f(x)==wfrec r x H;  wf(r) |] ==> f(a) = H a (cut (%x.f(x)) r a)";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[wfrec]) 1));
qed "def_wfrec";
