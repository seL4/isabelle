(*  Title:      HOL/wf.ML
    ID:         $Id$
    Author:     Tobias Nipkow, with minor changes by Konrad Slind
    Copyright   1992  University of Cambridge/1995 TU Munich

Wellfoundedness, induction, and  recursion
*)

open WF;

val H_cong = read_instantiate [("f","H")] (standard(refl RS cong RS cong));
val H_cong1 = refl RS H_cong;

(*Restriction to domain A.  If r is well-founded over A then wf(r)*)
val [prem1,prem2] = goalw WF.thy [wf_def]
 "[| r <= A Times A;  \
\    !!x P. [| ! x. (! y. (y,x) : r --> P(y)) --> P(x);  x:A |] ==> P(x) |]  \
\ ==>  wf(r)";
by (Clarify_tac 1);
by (rtac allE 1);
by (assume_tac 1);
by (best_tac (claset() addSEs [prem1 RS subsetD RS SigmaE2] addIs [prem2]) 1);
qed "wfI";

val major::prems = goalw WF.thy [wf_def]
    "[| wf(r);          \
\       !!x.[| ! y. (y,x): r --> P(y) |] ==> P(x) \
\    |]  ==>  P(a)";
by (rtac (major RS spec RS mp RS spec) 1);
by (blast_tac (claset() addIs prems) 1);
qed "wf_induct";

(*Perform induction on i, then prove the wf(r) subgoal using prems. *)
fun wf_ind_tac a prems i = 
    EVERY [res_inst_tac [("a",a)] wf_induct i,
           rename_last_tac a ["1"] (i+1),
           ares_tac prems i];

val prems = goal WF.thy "[| wf(r);  (a,x):r;  (x,a):r |] ==> P";
by (subgoal_tac "! x. (a,x):r --> (x,a):r --> P" 1);
by (blast_tac (claset() addIs prems) 1);
by (wf_ind_tac "a" prems 1);
by (Blast_tac 1);
qed "wf_asym";

val prems = goal WF.thy "[| wf(r);  (a,a): r |] ==> P";
by (rtac wf_asym 1);
by (REPEAT (resolve_tac prems 1));
qed "wf_irrefl";

(*transitive closure of a wf relation is wf! *)
val [prem] = goal WF.thy "wf(r) ==> wf(r^+)";
by (rewtac wf_def);
by (Clarify_tac 1);
(*must retain the universal formula for later use!*)
by (rtac allE 1 THEN assume_tac 1);
by (etac mp 1);
by (res_inst_tac [("a","x")] (prem RS wf_induct) 1);
by (rtac (impI RS allI) 1);
by (etac tranclE 1);
by (Blast_tac 1);
by (Blast_tac 1);
qed "wf_trancl";


(*----------------------------------------------------------------------------
 * Minimal-element characterization of well-foundedness
 *---------------------------------------------------------------------------*)

val wfr::_ = goalw WF.thy [wf_def]
    "wf r ==> x:Q --> (? z:Q. ! y. (y,z):r --> y~:Q)";
by (rtac (wfr RS spec RS mp RS spec) 1);
by (Blast_tac 1);
val lemma1 = result();

goalw WF.thy [wf_def]
    "!!r. (! Q x. x:Q --> (? z:Q. ! y. (y,z):r --> y~:Q)) ==> wf r";
by (Clarify_tac 1);
by (dres_inst_tac [("x", "{x. ~ P x}")] spec 1);
by (Blast_tac 1);
val lemma2 = result();

goal WF.thy "wf r = (! Q x. x:Q --> (? z:Q. ! y. (y,z):r --> y~:Q))";
by (blast_tac (claset() addSIs [lemma1, lemma2]) 1);
qed "wf_eq_minimal";

(*---------------------------------------------------------------------------
 * Wellfoundedness of subsets
 *---------------------------------------------------------------------------*)

goal thy "!!r. [| wf(r);  p<=r |] ==> wf(p)";
by (full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by (Fast_tac 1);
qed "wf_subset";

(*---------------------------------------------------------------------------
 * Wellfoundedness of the empty relation.
 *---------------------------------------------------------------------------*)

goal thy "wf({})";
by (simp_tac (simpset() addsimps [wf_def]) 1);
qed "wf_empty";
AddSIs [wf_empty];

(*---------------------------------------------------------------------------
 * Wellfoundedness of `insert'
 *---------------------------------------------------------------------------*)

goal WF.thy "wf(insert (y,x) r) = (wf(r) & (x,y) ~: r^*)";
by (rtac iffI 1);
 by (blast_tac (claset() addEs [wf_trancl RS wf_irrefl] 
	addIs [rtrancl_into_trancl1,wf_subset,impOfSubs rtrancl_mono]) 1);
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal]) 1);
by Safe_tac;
by (EVERY1[rtac allE, atac, etac impE, Blast_tac]);
by (etac bexE 1);
by (rename_tac "a" 1);
by (case_tac "a = x" 1);
 by (res_inst_tac [("x","a")]bexI 2);
  by (assume_tac 3);
 by (Blast_tac 2);
by (case_tac "y:Q" 1);
 by (Blast_tac 2);
by (res_inst_tac [("x","{z. z:Q & (z,y) : r^*}")] allE 1);
 by (assume_tac 1);
by (thin_tac "! Q. (? x. x : Q) --> ?P Q" 1);	(*essential for speed*)
(*Blast_tac with new substOccur fails*)
by (best_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
qed "wf_insert";
AddIffs [wf_insert];

(*** acyclic ***)

goalw WF.thy [acyclic_def]
 "!!r. wf r ==> acyclic r";
by (blast_tac (claset() addEs [wf_trancl RS wf_irrefl]) 1);
qed "wf_acyclic";

goalw WF.thy [acyclic_def]
  "acyclic(insert (y,x) r) = (acyclic r & (x,y) ~: r^*)";
by (simp_tac (simpset() addsimps [trancl_insert]) 1);
by (blast_tac (claset() addEs [make_elim rtrancl_trans]) 1);
qed "acyclic_insert";
AddIffs [acyclic_insert];

goalw WF.thy [acyclic_def] "acyclic(r^-1) = acyclic r";
by (simp_tac (simpset() addsimps [trancl_converse]) 1);
qed "acyclic_converse";

(** cut **)

(*This rewrite rule works upon formulae; thus it requires explicit use of
  H_cong to expose the equality*)
goalw WF.thy [cut_def]
    "(cut f r x = cut g r x) = (!y. (y,x):r --> f(y)=g(y))";
by (simp_tac (HOL_ss addsimps [expand_fun_eq]) 1);
qed "cuts_eq";

goalw WF.thy [cut_def] "!!x. (x,a):r ==> (cut f r a)(x) = f(x)";
by (asm_simp_tac HOL_ss 1);
qed "cut_apply";

(*** is_recfun ***)

goalw WF.thy [is_recfun_def,cut_def]
    "!!f. [| is_recfun r H a f;  ~(b,a):r |] ==> f(b) = arbitrary";
by (etac ssubst 1);
by (asm_simp_tac HOL_ss 1);
qed "is_recfun_undef";

(*** NOTE! some simplifications need a different finish_tac!! ***)
fun indhyp_tac hyps =
    (cut_facts_tac hyps THEN'
       DEPTH_SOLVE_1 o (ares_tac [TrueI] ORELSE'
                        eresolve_tac [transD, mp, allE]));
val wf_super_ss = HOL_ss addSolver indhyp_tac;

val prems = goalw WF.thy [is_recfun_def,cut_def]
    "[| wf(r);  trans(r);  is_recfun r H a f;  is_recfun r H b g |] ==> \
    \ (x,a):r --> (x,b):r --> f(x)=g(x)";
by (cut_facts_tac prems 1);
by (etac wf_induct 1);
by (REPEAT (rtac impI 1 ORELSE etac ssubst 1));
by (asm_simp_tac (wf_super_ss addcongs [if_cong]) 1);
qed_spec_mp "is_recfun_equal";


val prems as [wfr,transr,recfa,recgb,_] = goalw WF.thy [cut_def]
    "[| wf(r);  trans(r); \
\       is_recfun r H a f;  is_recfun r H b g;  (b,a):r |] ==> \
\    cut f r b = g";
val gundef = recgb RS is_recfun_undef
and fisg   = recgb RS (recfa RS (transr RS (wfr RS is_recfun_equal)));
by (cut_facts_tac prems 1);
by (rtac ext 1);
by (asm_simp_tac (wf_super_ss addsimps [gundef,fisg]) 1);
qed "is_recfun_cut";

(*** Main Existence Lemma -- Basic Properties of the_recfun ***)

val prems = goalw WF.thy [the_recfun_def]
    "is_recfun r H a f ==> is_recfun r H a (the_recfun r H a)";
by (res_inst_tac [("P", "is_recfun r H a")] selectI 1);
by (resolve_tac prems 1);
qed "is_the_recfun";

val prems = goal WF.thy
 "[| wf(r);  trans(r) |] ==> is_recfun r H a (the_recfun r H a)";
  by (cut_facts_tac prems 1);
  by (wf_ind_tac "a" prems 1);
  by (res_inst_tac [("f","cut (%y. H (the_recfun r H y) y) r a1")]
                   is_the_recfun 1);
  by (rewtac is_recfun_def);
  by (stac cuts_eq 1);
  by (rtac allI 1);
  by (rtac impI 1);
  by (res_inst_tac [("f1","H"),("x","y")](arg_cong RS fun_cong) 1);
  by (subgoal_tac
         "the_recfun r H y = cut(%x. H(cut(the_recfun r H y) r x) x) r y" 1);
  by (etac allE 2);
  by (dtac impE 2);
  by (atac 2);
  by (atac 3);
  by (atac 2);
  by (etac ssubst 1);
  by (simp_tac (HOL_ss addsimps [cuts_eq]) 1);
  by (rtac allI 1);
  by (rtac impI 1);
  by (asm_simp_tac (wf_super_ss addsimps[cut_apply,is_recfun_cut,cuts_eq]) 1);
  by (res_inst_tac [("f1","H"),("x","ya")](arg_cong RS fun_cong) 1);
  by (fold_tac [is_recfun_def]);
  by (asm_simp_tac (wf_super_ss addsimps[cut_apply,is_recfun_cut,cuts_eq]) 1);
qed "unfold_the_recfun";

val unwind1_the_recfun = rewrite_rule[is_recfun_def] unfold_the_recfun;

(*--------------Old proof-----------------------------------------------------
val prems = goal WF.thy
    "[| wf(r);  trans(r) |] ==> is_recfun r H a (the_recfun r H a)";
by (cut_facts_tac prems 1);
by (wf_ind_tac "a" prems 1);
by (res_inst_tac [("f", "cut (%y. wftrec r H y) r a1")] is_the_recfun 1); 
by (rewrite_goals_tac [is_recfun_def, wftrec_def]);
by (stac cuts_eq 1);
(*Applying the substitution: must keep the quantified assumption!!*)
by (EVERY1 [Clarify_tac, rtac H_cong1, rtac allE, atac,
            etac (mp RS ssubst), atac]); 
by (fold_tac [is_recfun_def]);
by (asm_simp_tac (wf_super_ss addsimps[cut_apply,is_recfun_cut,cuts_eq]) 1);
qed "unfold_the_recfun";
---------------------------------------------------------------------------*)

(** Removal of the premise trans(r) **)
val th = rewrite_rule[is_recfun_def]
                     (trans_trancl RSN (2,(wf_trancl RS unfold_the_recfun)));

goalw WF.thy [wfrec_def]
    "!!r. wf(r) ==> wfrec r H a = H (cut (wfrec r H) r a) a";
by (rtac H_cong 1);
by (rtac refl 2);
by (simp_tac (HOL_ss addsimps [cuts_eq]) 1);
by (rtac allI 1);
by (rtac impI 1);
by (simp_tac(HOL_ss addsimps [wfrec_def]) 1);
by (res_inst_tac [("a1","a")] (th RS ssubst) 1);
by (atac 1);
by (forward_tac[wf_trancl] 1);
by (forward_tac[r_into_trancl] 1);
by (asm_simp_tac (HOL_ss addsimps [cut_apply]) 1);
by (rtac H_cong 1);    (*expose the equality of cuts*)
by (rtac refl 2);
by (simp_tac (HOL_ss addsimps [cuts_eq, cut_apply, r_into_trancl]) 1);
by (Clarify_tac 1);
by (res_inst_tac [("r","r^+")] is_recfun_equal 1);
by (atac 1);
by (rtac trans_trancl 1);
by (rtac unfold_the_recfun 1);
by (atac 1);
by (rtac trans_trancl 1);
by (rtac unfold_the_recfun 1);
by (atac 1);
by (rtac trans_trancl 1);
by (rtac transD 1);
by (rtac trans_trancl 1);
by (forw_inst_tac [("a","ya")] r_into_trancl 1);
by (atac 1);
by (atac 1);
by (forw_inst_tac [("a","ya")] r_into_trancl 1);
by (atac 1);
qed "wfrec";

(*--------------Old proof-----------------------------------------------------
goalw WF.thy [wfrec_def]
    "!!r. wf(r) ==> wfrec r H a = H (cut (wfrec r H) r a) a";
by (etac (wf_trancl RS wftrec RS ssubst) 1);
by (rtac trans_trancl 1);
by (rtac (refl RS H_cong) 1);    (*expose the equality of cuts*)
by (simp_tac (HOL_ss addsimps [cuts_eq, cut_apply, r_into_trancl]) 1);
qed "wfrec";
---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------
 * This form avoids giant explosions in proofs.  NOTE USE OF == 
 *---------------------------------------------------------------------------*)
val rew::prems = goal WF.thy
    "[| f==wfrec r H;  wf(r) |] ==> f(a) = H (cut f r a) a";
by (rewtac rew);
by (REPEAT (resolve_tac (prems@[wfrec]) 1));
qed "def_wfrec";


(**** TFL variants ****)

goal WF.thy
    "!R. wf R --> (!P. (!x. (!y. (y,x):R --> P y) --> P x) --> (!x. P x))";
by (Clarify_tac 1);
by (res_inst_tac [("r","R"),("P","P"), ("a","x")] wf_induct 1);
by (assume_tac 1);
by (Blast_tac 1);
qed"tfl_wf_induct";

goal WF.thy "!f R. (x,a):R --> (cut f R a)(x) = f(x)";
by (Clarify_tac 1);
by (rtac cut_apply 1);
by (assume_tac 1);
qed"tfl_cut_apply";

goal WF.thy "!M R f. (f=wfrec R M) --> wf R --> (!x. f x = M (cut f R x) x)";
by (Clarify_tac 1);
by (etac wfrec 1);
qed "tfl_wfrec";
